signature MatchArgBlg =
  sig
    val matchArgBlg : PreArgBlg.PreArgBlg -> 'a MatchData.Collector -> 'a 
      -> MatchData.Content -> DocDtd.Dtd -> 'a 
  end
structure MatchArgBlg : MatchArgBlg =
  struct
    open DocDtd Errors IntLists MatchData MatchUtil GrepOptions MatchOptions
      
    val THIS_MODULE = "MatchArgBlg"
    val O_TS_MATCH = ref 5

    fun matchArgBlg pre reportOne r f dtd =
      let
	val (sigVec,yVec,rhsVec,tpVec,otherRules,otherY0s,qr0,ql0info,
	     doMatch,
	     incomingXVec,regExpNameRules,target_ys_of_x,formulas) = pre 
	val (primaries,secondaries) = Vector.sub(doMatch,0)
	val (f1,f2s) = Vector.sub(formulas,0)
	val (_,getIntersection,_,_,_,yFs_for_p,_,yFs_for_q,
	     getQindex,getQstate,getQinfo,setQinfo,
	     runArg,multRunArg,debugArg,down,side,sideMatchInfo,debugBlg) = 
	  ArgBlg.argBlg 
	  (sigVec,yVec,rhsVec,tpVec,
	   otherRules,otherY0s,qr0,ql0info,
	   incomingXVec,regExpNameRules,target_ys_of_x)
	  dtd
		
	local
  	  fun matches q =
	    case getQinfo q of 
	      (_,_,_,SOME d) => d
	    | (a,b,c,NONE) => 
		let 
		  val ys = getQstate q
		  val d = Formula.eval (fn ys1 => capIntLists(ys,ys1)<>nil) f1
		in
		  d before setQinfo(q,(a,b,c,SOME d))
		end

	  (*--------------------------------------------------------------*)
	  (* q = current state                                            *)
	  (* f = current forest                                           *)
	  (* t = current tree                                             *)
	  (* r = already accumulated matches                              *)
	  (* s = whether a subtree matches                                *)
	  (* l = label for a subtree                                      *)
	  (*--------------------------------------------------------------*)
	  fun deltaF (r,q,ls,f) =
	    let 
	      val len = Vector.length f
	      fun doit (r,s,q,i) = 
		if i>=len then (r,s)
		else let val (pos,t) = Vector.sub(f,i)
			 val l as LABEL(qr,p,_,_,_,_) = Vector.sub(ls,i)
			 val qq = getIntersection (q,qr)
			 val match = matches qq
			 val (r1,s1) = 
			   case !O_MATCH_SELECT 
			     of INNER => let val (rt,st) = deltaT(r,qq,l,t)
					 in if st orelse not match then (rt,s orelse st) 
					    else (reportOne((pos,t),rt),true)
					 end
			   | OUTER => if match then (reportOne((pos,t),r),true)
				      else deltaT(r,qq,l,t)
			   | ALL => let val (r1,s1) = 
					if match then (reportOne((pos,t),r),true)
					else (r,s)
					val (rt,st) = deltaT(r1,qq,l,t)
				    in (rt,st orelse s1)
				    end
			 val i = i+1
		     in
		       if i >= len then (r1,s1)
		       else
			 let
			   val q1 = side (qq,p)
			 in 
			   doit(r1,s1,q1,i)
			 end
		     end
	    in doit(r,false,q,0)
	    end
	  and deltaT (r,qq,LABEL(qr,p,pa,qr1,pc,ls),t) =
	    case t
	      of T_PI(_,cont) => 
		let 
		  val q0 = down(piIdx,qq,p)
		  val q1 = side(q0,pa)
		  val qq1 = getIntersection (q1,qr1)
		  val qc0 = down(contentIdx,qq1,pc)
		  val (rf,sf) = deltaF(r,qc0,ls,cont)
		in (rf,sf)
		end
	    | T_ELEM(a,atts,cont) => 
		let 
		  val q0 = down(a,qq,p)
		  val q1 = side(q0,pa)
		  val qq1 = getIntersection (q1,qr1)
		  val qc0 = down(contentIdx,qq1,pc)
		  val (rf,sf) = deltaF(r,qc0,ls,cont)
		in (rf,sf)
		end
	    | _ => (r,false)
	      
	in 
	  val runBlg = deltaF
	end
            
	val (ls,qr) = runArg(getQindex qr0,f)
	val _ = debugArg()
	val yrs = getQstate qr
	val ql0 = foldl 
	  (fn ((posFs,negF,posF),ys) 
	   => if (capIntLists(yrs,negF)<>nil orelse 
		  List.exists (fn posF => capIntLists(yrs,posF)=nil) posFs) then ys
	      else cupIntLists(ys,posF))
	  nil ql0info 
	val r1 = if null ql0 then r else #1(runBlg(r,getQindex ql0,ls,f))
	val _ = debugBlg()
      in r1
      end
  end
