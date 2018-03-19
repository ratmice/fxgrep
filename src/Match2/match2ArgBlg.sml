structure Match2ArgBlg =
  struct
    open DocDtd Errors IntLists MatchData MatchUtil GrepOptions MatchOptions
      
    val THIS_MODULE = "Match2ArgBlg"
    val O_TS_MATCH = ref 5

    fun up2Levels_ys_of_y (ys_of_y,qq1_ys,qq_ys) y =
      let
	val cont_target_ys = IntLists.capIntLists (Vector.sub (ys_of_y,y),qq1_ys)
	val element_ys = List.concat
			   (List.map 
			    (fn y => Vector.sub (ys_of_y,y)) cont_target_ys)
	val ys = IntLists.capIntLists (element_ys,qq_ys)
      in
	ys
      end

    fun matchArgBlg pre (enc,f) reportMatchTable dtd = 
      let
	val (sigVec,yVec,rhsVec,tpVec,
	     otherRules,otherY0s,qr0,ql0info,
	     doMatch,incomingXVec,regExpNameRules,ys_of_y,formulas) = 
	  pre : PreArgBlg.PreArgBlg 

	val (primaries,secondaries) = Vector.sub(doMatch,0)
	val (f1,f2s) = Vector.sub(formulas,0)
	val (_,getIntersection,getPstate,Fs_for_rule,xs_of_p,yFs_for_p,trans_for_y,yFs_for_q,
	     getQindex,getQstate,getQinfo,setQinfo,runArg,
	     multRunArg,debugArg,down,side,sideMatchInfo,debugBlg) = 
	  ArgBlg.argBlg 
	  (sigVec,yVec,rhsVec,tpVec,
	   otherRules,otherY0s,qr0,ql0info,
	   incomingXVec,regExpNameRules,ys_of_y)
	  dtd

	val suggestedSize = 100
	val matchTable = 
	  DynamicArray.array 
	  (suggestedSize,
	   ((("uninitialized",0,0),MatchData.T_TEXT #[]),IntListMap.empty))

	local 
	  fun matches q = 
	    case getQinfo q of 
	      (_,_,_,SOME d) => d
	    | (a,b,c,NONE) => 
		let 
		  val ys = getQstate q
		  val (m,prim,sec) = 
		    Transitions.getMatchInfo (ys,(primaries,secondaries),(f1,f2s))
		  val d = (m,prim,sec)
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
	  fun deltaF (j,q,ls,f) =
	    let
	      val len = Vector.length f
	      fun doit (j,dict,q,i) = 
		if i >= len then (j,dict)
		else 
		  let
		    val (pos,t) = Vector.sub(f,i)
		    val l as LABEL(qr,p,_,_,_,_) = Vector.sub(ls,i)
		    val qq = getIntersection (q,qr)
		    val (match,yTargets,secMatches) = matches qq
		    val (j,dict) = 
		      Match2.addMatches (match,yTargets,secMatches,matchTable,j,dict,pos,t)
		    val (j,dictT) = deltaT (j,qq,l,t)
		    val dict =
		      Match2.matchMapUnion matchTable (dict,dictT) 
		      (IntListMap.unionWith NodeSet.union) DynamicArray.sub 
		      DynamicArray.update
		    val i = i+1
		    val ys_of_qq = getQstate qq
		  in
		    if i >= len then
		      (j,(IntListMap.filteri
			  (fn (y,_) => IntLists.inIntList (y,ys_of_qq))
			  dict))
		    else
		      let 			  
			val (dict,q1) = 
			  sideMatchInfo (IntListMap.unionWith NodeSet.union)(dict,qq)
		      in
			doit (j,dict,q1,i)
		      end
		  end
	    in 
	      doit (j,IntListMap.empty,q,0)
	    end
	  and deltaT (j,qq,LABEL(qr,p,pa,qr1,pc,ls),t) =
	    let
	      fun matchConjunction dict ks =
		(* primaries and secondaries can also meet at
		 conjunction nodes, even if they do not correspond to a
		 same nfa state. (e.g. a[&c]//b for
		 <a><b><c/></b></a>) *)
		List.app
		(fn k =>
		 let
		   val (_,_,_,yss) = Fs_for_rule k
		 in
		   if List.length yss <= 1 then ()
		   else (*conjunction*)
		     let
		       val (allSecondaries,pss) =
			 List.foldl 
			 (fn (ys,(s,pss)) =>
			  let
			    (* primaries and secondaries corresponding
			     to final states of one of the regular
			     expressions in the conjunction *)
			    val (s,p) = 
			      List.foldl 
			      (fn (y,(s1,p1)) =>
			       case IntListMap.find (dict,y) of
				 SOME (p2,s2) => 
				   (IntListMap.unionWith NodeSet.union (s1,s2),IntSet.union (p1,p2))
			       | NONE => (s1,p1)) (s,IntSet.empty) ys
			  in
			    (s,(p,s)::pss)
			  end)
			 (IntListMap.empty,nil) yss
		     in
		       List.app
		       (* all the primaries of one re belong together
                          with all the secondaries of all the other re-s in the conjunction *)
		       (fn (primaries,secondaries) =>
			let
			  val restSecondaries = 
			    IntListMap.foldli
			    (fn (i,secondaries,secDiff) => 
			     IntListMap.insert 
			     (secDiff,i,
			      NodeSet.difference
			      (Option.valOf (IntListMap.find (allSecondaries,i)),secondaries)))
			    allSecondaries secondaries
			in
			  IntSet.app
			  (fn i =>
			   let 
			     val (t,ts) = DynamicArray.sub (matchTable,i)
			   in
			     DynamicArray.update 
			     (matchTable,i,
			      (t,IntListMap.unionWith NodeSet.union (ts,restSecondaries)))
			   end) primaries
			end) pss
		     end
		 end) ks
	    in
	      case t of 
		T_PI(_,cont) => 
		  let 
		    val q0 = down (piIdx,qq,p)
		    val q1 = side (q0,pa)
		    val qq1 = getIntersection (q1,qr1)
		    val qc0 = down(contentIdx,qq1,pc)
		    val (j,dict) = deltaF (j,qc0,ls,cont)
		    val ks = getPstate pc
		    val _ = matchConjunction dict ks
		    val dict = 
		      Transitions.matchMapTransition Match2.secUnion
		      (up2Levels_ys_of_y (ys_of_y,getQstate qq1,getQstate qq)) 
		      dict 
		  in 
		    (j,dict)
		  end
	      | T_ELEM(a,atts,cont) => 
		  let 
		    val q0 = down (a,qq,p)
		    val q1 = side (q0,pa)
		    val qq1 = getIntersection (q1,qr1)
		    val qc0 = down(contentIdx,qq1,pc)
		    val (j,dict) = deltaF (j,qc0,ls,cont)
		    val ks = getPstate pc
		    val _ = matchConjunction dict ks
		    val dict = 
		      Transitions.matchMapTransition Match2.secUnion
		      (up2Levels_ys_of_y (ys_of_y,getQstate qq1,getQstate qq)) 
		      dict 
		  in 
		    (j,dict)
		  end
	      | _ => (j,IntListMap.empty)
	    end
	in 
	  val runBlg = deltaF
	end
            
        val (ls,qr) = runArg (getQindex qr0,f)
	val _ = debugArg()
	val yrs = getQstate qr
	val ql0 = foldl 
	  (fn ((posFs,negF,posF),ys) 
	   => if (capIntLists(yrs,negF)<>nil orelse 
		  List.exists (fn posF => capIntLists(yrs,posF)=nil) posFs) then ys
	      else cupIntLists(ys,posF))
	  nil ql0info 
	val (j,dict) = runBlg (0,getQindex ql0,ls,f)
	val _ = debugBlg()
	val _ = reportMatchTable (matchTable,j,enc)
      in 
	()
      end

   end
