structure Match2 =
  struct
    open UtilString

    val THIS_MODULE = "Match2"

    val secUnion = IntListMap.unionWith NodeSet.union

    fun printDict (s,dict) =
      let
	val _ = print (s^" = {")
	val _ = IntListMap.appi (fn (y,_) => print ((Int.toString y)^";")) dict
	val _ = print "}\n"
      in
	()
      end

    fun matchMapUnion matchTable (matchMap1,matchMap2) secUnion sub update =
      IntListMap.unionWith
	(fn ((t1,t1'),(t2,t2')) =>
	  let
            val _ = 
                IntSet.app
		  (fn j =>
		      let 
                        val (t,targets') = sub (matchTable,j)
                        val _ = update (matchTable,j, (t,secUnion (targets',t2')))
		      in
                        ()
		      end) t1
            val _ = 
                IntSet.app
		  (fn j =>
		      let 
                        val (t,targets') = sub (matchTable,j)
                        val _ = update (matchTable,j, (t,secUnion (targets',t1')))
		      in
                        ()
		      end) t2
	  in
	    (IntSet.union (t1,t2),secUnion (t1',t2'))
	  end)
	(matchMap1,matchMap2)

    fun addPrimaryMatch targets (matchTable,j) matchMap (pos,t) =
      let
	val (matchMap,secMatches) =
	  List.foldl
	    (fn (y,(dict,secMatches)) =>
		let
		  val (matchInfo,secMatches) = 
		    case IntListMap.find (dict,y) of
		      SOME (matches,matches') =>
			((IntSet.add (matches,j),matches'),
			 IntListMap.unionWith NodeSet.union (secMatches,matches'))
		    | NONE => 
			((IntSet.singleton j,IntListMap.empty),secMatches)
		in
		  (IntListMap.insert (dict,y,matchInfo),secMatches)
		end) (matchMap,IntListMap.empty) targets
	val _ = DynamicArray.update (matchTable,j, ((pos,t),secMatches))
      in
	matchMap
      end

    fun addSecondaryMatches secMatches matchTable matchMap (pos,t) =
      (* matchTable stores the matches found so far *)
      (* matchMap stores the match infomation in the current state *)
      let
        val (matchMap,primaries) = 
	(* primaries is a map collecting primary matches (as indices
	in matchTable) which form a binary match with the current node *)
	  Vector.foldli
	  (fn (secOrd,ys,(matchMap,primaries)) =>
	   List.foldl
	   (fn (y,(matchMap,primaries)) =>
	    let 
	      val (matchInfo,primaries) =
		case (IntListMap.find (matchMap,y)) of
		  SOME (matches,matches') =>
		    ((matches,
		      case IntListMap.find (matches',secOrd) of
			SOME secSet => 
			  IntListMap.insert (matches',secOrd,NodeSet.add(secSet,(pos,t)))
		      | NONE => 
			  IntListMap.insert (matches',secOrd,NodeSet.singleton (pos,t))),
		     
		     IntSet.foldl
		     (fn (i,primaries) =>
		      case IntListMap.find (primaries,i) of
			SOME secOrds => IntListMap.insert (primaries,i,IntSet.add (secOrds,secOrd))
		      | NONE => IntListMap.insert (primaries,i,IntSet.singleton secOrd))
		     primaries matches)
		| NONE => 
		    ((IntSet.empty,IntListMap.singleton (secOrd,NodeSet.singleton(pos,t))),primaries) 
	    in
	      (IntListMap.insert (matchMap,y,matchInfo),primaries)
	    end)
	   (matchMap,primaries) ys)
	  (matchMap,IntListMap.empty) secMatches

        val _ = IntListMap.appi
	  (fn (j,secOrds) =>
	   let
	     val (t1,targets2) = DynamicArray.sub (matchTable,j)
	     val targets2 = 
	       IntSet.foldl
	       (fn (secOrd,targets2) =>
		case IntListMap.find (targets2,secOrd) of
		  SOME secSet => IntListMap.insert (targets2,secOrd,NodeSet.add(secSet,(pos,t)))
		| NONE => IntListMap.insert (targets2,secOrd,NodeSet.singleton (pos,t)))
	       targets2 secOrds
	     val _ = DynamicArray.update (matchTable,j,(t1,targets2))
	   in
	     ()
	   end) primaries
      in
	matchMap
      end

    fun addMatches (match,yTargets,secMatches,matchTable,j,dict,pos,t) =
      let
	val (j,dict) = 
	  if match then
	    let
	      val dict = addPrimaryMatch yTargets (matchTable,j) dict (pos,t)
	    in
	      (j+1,dict)
	    end
	  else (j,dict)
(* info for secondaries must be carried by all ys specified as secondaries, 
in order to meet their corresponding primaries; only info for primaries 
is carried by those ys which besides being specified as primaries also 
satisfy the formula *)
	val dict = addSecondaryMatches secMatches matchTable dict (pos,t)
      in
	(j,dict)
      end

    fun printMatchTable dtd (matchTable,noMatches,enc) =
      let
	val r0 = MatchReport2.reportStart enc	   
	fun doit (i,c,r) = 
	  if i >= noMatches then (c,r)
	  else 
	    let
	      val ((pos,t),secondaryMatches) = 
		DynamicArray.sub (matchTable,i)
	      val r2 =
		MatchReport2.report dtd (((pos,t),secondaryMatches),r)
	      val num = IntListMap.foldl (fn (s,c) => c+(NodeSet.numItems s)) 0 secondaryMatches
	    in
	      doit (i+1,c+num,r2)
	    end
	val (c,r) = doit (0,0,r0)
      in
	MatchReport2.reportFinish (c,r)
      end


  end
