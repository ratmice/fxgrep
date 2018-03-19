signature MatchAlg =
  sig
    val matchAlg : bool * PreAlg.PreAlg -> 
      'a MatchData.Collector -> 'a -> MatchData.Content -> DocDtd.Dtd -> 'a
  end

structure MatchAlg : MatchAlg =
  struct
    open DocDtd Errors IntLists MatchData MatchUtil GrepOptions 
      MatchOptions MatchReport MatchOutput Transitions
      
    val THIS_MODULE = "MatchAlg"
      
    fun matchAlg (isContentIgnoring,pre) reportOne r f dtd =
      let
	val (q0,down,downRegExpNames,up,
	     upRegExpNames,side,sideMatchInfo,text,
	     mightMatch,mightMatchAfterTag,mightMatchAfterAtts,
	     matches,elDictLookup,deltaA,transOnePass,debug) =
	  getTransitions pre
	  
	val report = ReportMatchUtil.reportMatches reportOne	 	    

	(*--------------------------------------------------------------*)
	(* q = current state                                            *)
	(* f = current forest                                           *)
	(* t = current tree                                             *)
	(* m = yet unreported matches                                   *)
	(* r = already accumulated matches                              *)
	(* s = whether a subtree matches                                *)
	(*--------------------------------------------------------------*)
	fun deltaF (m,r,q,f) =
	  let 
	    val len = Vector.length f
	    fun doit (m,r,s,q,i) = 
	      if i>=len then (m,r,s,q)
	      else 
		let 
		  val (pos,t) = Vector.sub(f,i)
		  val might = mightMatch q 
		  val m0 = if isSome m orelse might andalso !O_MATCH_SELECT<>INNER 
			     then SOME nil else m
		  val (mt,rt,st,p) = deltaT (m0,r,q,t)
		  val q1 = side(q,p)
		  val (match,_,_) = Vector.sub(matches q1,0)
		  val (m1,r1,s1) = 
		    case !O_MATCH_SELECT of 
		      INNER => 
			if st orelse not match then (NONE,rt,st orelse s) 
			else (NONE,reportOne((pos,t),rt),true)
		    | OUTER => 
			  (case m
			     of NONE => 
			       let val r1 = 
				 if match then reportOne((pos,t),rt)
				 else case mt
				   of NONE => rt
				 | SOME nil => rt
				 | SOME ms => report(MORE(NONE,ms),rt)
			       in (NONE,r1,false)
			       end
			   | SOME ms => 
			       let val ms1 = 
				 if match then ONE(pos,t)::ms
				 else case mt
				   of NONE => ms
				 | SOME nil => ms
				 | SOME ms2 => MORE(NONE,ms2)::ms
			       in (SOME ms1,rt,false)
			       end)
		    | ALL => 
			     case m
			       of NONE => 
				 let val r1 = 
				   if match then case mt
				     of NONE => reportOne((pos,t),rt)
				   | SOME nil => reportOne((pos,t),rt)
				   | SOME ms => report
				       (MORE(SOME(pos,t),ms),rt)
				   else case mt
				     of NONE => rt
				   | SOME nil => rt
				   | SOME ms => report(MORE(NONE,ms),rt)
				 in (NONE,r1,false)
				 end
			     | SOME ms => 
				 let val ms1 = 
				   if match then case mt of 
				     NONE => ONE(pos,t)::ms
				   | SOME nil => ONE(pos,t)::ms
				   | SOME ms2 => 
				       MORE(SOME(pos,t),ms2)::ms
				   else case mt of 
				     NONE => ms
				   | SOME nil => ms
				   | SOME ms2 => MORE(NONE,ms2)::ms
				 in (SOME ms1,rt,false)
				 end
		in doit(m1,r1,s1,q1,i+1)
		end
	  in doit(m,r,false,q,0)
	  end
	and deltaT (m,r,q,t) =
	  case t of 
	    T_TEXT txt => (m,r,false,text(q,txt))
	  | T_PI(target,cont) => 
	      let 
		val q0 = down(piIdx,q)
		val qa0 = down(attrsIdx,q0)
		val qa1 = deltaA(qa0,Vector.fromList[(targetIdxE,target)])
		val pa = up (attrsIdx,qa1)
		val q1 = side(q0,pa)
		val qc0 = down(contentIdx,q1)
		val (mf,rf,sf,qc1) = deltaF (m,r,qc0,cont)
		val pc = up(contentIdx,qc1)
		val q2 = side(q1,pc)
	      in (mf,rf,sf,up(piIdx,q2))
	      end
	  | T_ELEM(a,atts,cont) => 
	      let
		val (y0s_regExpRules,regExpRules) = elDictLookup (dtd,a)
		val q0 = downRegExpNames(a,q,y0s_regExpRules)
		val qa0 = down(attrsIdx,q0)
		val qa1 = deltaA(qa0,atts)
		val pa = up(attrsIdx,qa1)
		val q1 = side(q0,pa)
		val qc0 = down(contentIdx,q1)
		val (mf,rf,sf,qc1) = deltaF (m,r,qc0,cont)
		val pc = up(contentIdx,qc1)
		val q2 = side(q1,pc)
	      in 
		(mf,rf,sf,upRegExpNames(a,q2,regExpRules))
	      end
	and deltaA (q,atts) =
	  let val len = Vector.length atts
	    fun doit (q,i) = 
	      if i>=len then q
	      else let val (a,txt) = Vector.sub(atts,i) 
		       val qa0 = down(a,q)
		       val pa = text(qa0,txt)
		       val qa1 = side(qa0,pa)
		       val p = up(a,qa1)
		       val q1 = side (q,p)
		   in doit(q1,i+1)
		   end
	  in doit(q,0)
	  end

(* if for some query it is not necessary to look for the content of
the match, and the query can be answered in one pass, then the match
can be reported immediately after seing its tag and its attributes *)

	and deltaF1 (r,q,f) =
	  let 
	    val len = Vector.length f
	    fun doit (r,q,i) = 
	      if i>=len then (r,q)
	      else let val (pos,t) = Vector.sub(f,i)
		       val (rt,p) = deltaT1 (r,q,(pos,t))
		       val q1 = side(q,p)
		   in doit(rt,q1,i+1)
		   end
	  in doit(r,q,0)
	  end
	and deltaT1 (r,q,(pos,t)) =
	  case t
	    of T_TEXT txt =>
	      let
		val p = text(q,txt)
		val (match,_,_) = Vector.sub(matches (side (q,p)),0)
		val r = 
		  if match then reportOne((pos,t),r)
		  else r
	      in
		(r,p)
	      end

	  | T_PI(target,cont) => 
	      let 
		val q0 = down(piIdx,q)
		val qa0 = down(attrsIdx,q0)
		val qa1 = deltaA(qa0,Vector.fromList[(targetIdxE,target)])
		val pa = up(attrsIdx,qa1)
		val q1 = side(q0,pa)
		val might =  
		  (mightMatchAfterTag q0) andalso 
		  (mightMatchAfterAtts q1)
		val r1 = 
		  if might then reportOne((pos,t),r)
		  else r
		val qc0 = down(contentIdx,q1)
		val (rf,qc1) = deltaF1 (r1,qc0,cont)
		val pc = up(contentIdx,qc1)
		val q2 = side(q1,pc)
	      in (rf,up(piIdx,q2))
	      end
	  | T_ELEM(a,atts,cont) => 
	      let 
		val (y0s_regExpRules,regExpRules) = elDictLookup (dtd,a)
		val q0 = downRegExpNames(a,q,y0s_regExpRules)
		val qa0 = down(attrsIdx,q0)
		val qa1 = deltaA(qa0,atts)
		val pa = up(attrsIdx,qa1)
		val q1 = side(q0,pa)
		val might =  
		  (mightMatchAfterTag q0) andalso 
		  (mightMatchAfterAtts q1)
		val r1 = 
		  if might then reportOne((pos,t),r)
		  else r
		val qc0 = down(contentIdx,q1)
		val (rf,qc1) = deltaF1 (r1,qc0,cont)
		val pc = up(contentIdx,qc1)
		val q2 = side(q1,pc)
	      in 
		(rf,upRegExpNames(a,q2,regExpRules))
	      end
      
	val (m1,r1,_,_) = 
	  if isContentIgnoring andalso ((!O_MATCH_SELECT)=ALL) then
	    let
	      val (r,q) = deltaF1 (r,q0,f)
	    in
	      (NONE,r,false,q)
	    end
	  else deltaF (NONE,r,q0,f)
		
	val _ = if isSome m1 then raise InternalError 
	  (THIS_MODULE,"matchAlg","m1 is not NONE after matching") else ()
	  
      (*---------------------------------------------------*)
      (* possibly do some debugging output                 *)
      (*---------------------------------------------------*)
	val _ = debug()
      in 
	r1
      end
  end
