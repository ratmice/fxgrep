structure Match2Alg =
  struct
    open DocDtd Errors IntLists MatchData MatchUtil GrepOptions 
      MatchOptions MatchOutput
      Transitions

    val THIS_MODULE = "Match2Alg"

    fun matchAlg pre (enc,f) reportMatchTable dtd =
      let
	val (q0,down,downRegExpNames,up,
	     upRegExpNames,side,sideMatchInfo,text,
	     mightMatch,mightMatchAfterTag,mightMatchAfterAtts,
	     matches,elDictLookup,deltaA,transOnePass,debug) =
	  getTransitions pre
	  
	val suggestedSize = 100
	val matchTable = 
	  DynamicArray.array 
	  (suggestedSize,
	   ((("uninitialized",0,0),MatchData.T_TEXT #[]),IntListMap.empty))

	(*--------------------------------------------------------------*)
	(* j = current number                                           *)
	(* q = current state                                            *)
	(* f = current forest                                           *)
	(*--------------------------------------------------------------*)
	fun deltaF (j,q,f) =
	  let 
	    val len = Vector.length f
	    fun doit (j,dict,q,i) = 
	      (* i is the index of the son to be processed *)
	      (* j is the number of primary matches seen so far *)
	      if i>=len 
		then (j,dict,q)
	      else 

		let
		  val (pos,t) = Vector.sub (f,i)
		  val (j,dictT,p) = deltaT (j,q,t)
		  val (dict1,q1) = 
		    sideMatchInfo (matchMapTransition Match2.secUnion) (dict,q,p)
		  val dictT1 =
		    matchMapTransition Match2.secUnion (transOnePass q1) dictT 
		  val dict =
		    Match2.matchMapUnion matchTable (dict1,dictT1) 
		    (IntListMap.unionWith NodeSet.union) DynamicArray.sub DynamicArray.update
		  val (match,yTargets,secMatches) = Vector.sub(matches q1,0)
		  val (j,dict) = Match2.addMatches (match,yTargets,secMatches,matchTable,j,dict,pos,t)
		in 
		  doit (j,dict,q1,i+1)
		end
	  in 
	    doit (j,IntListMap.empty,q,0)
	  end
	and deltaT (j,q,t) =
	  case t
	    of T_TEXT txt => 
	      (j,IntListMap.empty,text (q,txt))
	  | T_PI(target,cont) => 
	      let 
		val q0 = down (piIdx,q)
		val qa0 = down (attrsIdx,q0)
		val qa1 = deltaA (qa0,Vector.fromList[(targetIdxE,target)])
		val pa = up (attrsIdx,qa1)
		val q1 = side (q0,pa)
		val qc0 = down (contentIdx,q1)
		val (j,dict,qc1) = deltaF (j,qc0,cont)
		val pc = up (contentIdx,qc1)
		val q2 = side (q1,pc)
		val dict = 
		  matchMapTransition Match2.secUnion (transOnePass q2) dict 
	      in 
		(j,dict,up(piIdx,q2))
	      end
	  | T_ELEM(a,atts,cont) => 
	      let
		val (y0s_regExpRules,regExpRules) = elDictLookup (dtd,a)
		val q0 = downRegExpNames (a,q,y0s_regExpRules)
		val qa0 = down (attrsIdx,q0)
		val qa1 = deltaA (qa0,atts)
		val pa = up (attrsIdx,qa1)
		val q1 = side (q0,pa)
		val qc0 = down (contentIdx,q1)
		val (j,dict,qc1) = deltaF (j,qc0,cont)
		val pc = up (contentIdx,qc1)
		val q2 = side (q1,pc)
		val dict = 
		  matchMapTransition Match2.secUnion (transOnePass q2) dict 
	      in 
		(j,dict,upRegExpNames (a,q2,regExpRules))
	      end

	val (j,dict,q) = deltaF (0,(*getQindex*) q0,f)
	
	val _ = reportMatchTable (matchTable,j,enc)
		  

	(*---------------------------------------------------*)
	(* possibly do some debugging output                 *)
	(*---------------------------------------------------*)
	val _ = debug ()
      in 
	()
      end
  end
