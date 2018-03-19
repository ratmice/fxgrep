signature PreAlg =
  sig

    type YVector = (int * (int * int list) list * int list * int list * int) vector
    type Q0 = int list

    type PreAlg = YVector * Pre.AVector  * Pre.RhsVector * Pre.TextPatternsVector 
      * Pre.OtherRules * Pre.OtherY0s * Q0 * 
      Pre.DoMatch vector * 
      Pre.YTargetsVector * Pre.RegExpNamesInfo * 
      Pre.YsFormula option Pre.Spec *
      Pre.YsFormula Pre.Spec * Pre.YsFormula Pre.Spec * Pre.YsFormula Pre.Spec

    val multPreAlg : Pre.Intervals -> GramFlatten.Flat * GramData.MatchSpec list -> PreAlg

    val preAlg : GramFlatten.Flat * GramData.MatchSpec -> PreAlg
            
  end

structure PreAlg : PreAlg =
  struct
    open GramData GramTables GramUtil GrepOptions IntLists UtilInt

    val THIS_MODULE = "PreAlg"      

    type YVector = (int * (int * int list) list * int list * int list * int) vector
    type Q0 = int list
    type 'a Spec = ('a * 'a vector) vector
    type PreAlg = YVector * Pre.AVector  * Pre.RhsVector * Pre.TextPatternsVector 
      * Pre.OtherRules * Pre.OtherY0s * Q0 * 
      Pre.DoMatch vector * 
      Pre.YTargetsVector * Pre.RegExpNamesInfo * 
      Pre.YsFormula option Spec *
      Pre.YsFormula Spec * Pre.YsFormula Spec * Pre.YsFormula Spec

    type QualifiersInfo = (int*((int*int)list)) list

    fun doYVec(max,xArr,rulArr,(* in general a list with an item for each match pattern *)
	       xreVec,patternNum,rules,xXaXcs,matchSpecs) =
      (*--------------------------------------------------------------*)
      (* yVec[y] = ({(x,y1)|(y,x,y1)in delta_j},                      *) 
      (*            {y_(0,j)|(y,x,y1)in delta_j,                      *)
      (*                     Rules[k]=x-><... && _ re_j && ...>},     *)
      (*            {k|(y,x,y1)in delta_j,Rules[k]=x->"..."})         *)
      (*--------------------------------------------------------------*)
      let
	val numY = Vector.foldl (fn ((_,berry),num) => num+Array.length berry) 0 xreVec
	val yArr = Array.array (numY,(~1,nil,nil,nil,~1))
	val reArr = Array.array (Vector.length xreVec,(0,nil))

	val (targets,doMatch,preForm1) = Pre.initTargets matchSpecs

	val preForm = Pre.mapSpec Formula.preFormula preForm1
        val preFormXs = 
	  Pre.mapSpec
	  (fn preForm => ListMergeSort.sort Int.>	  
	   (case preForm of
	      SOME f => Formula.formulaVars f
	    | NONE => nil)) preForm
	val preFormMap = 
	  Pre.mapSpec
	  (fn preFormXs =>
	   List.foldl (fn (x,m) => IntListMap.insert(m,x,IntLists.emptyIntList))
	   IntListMap.empty preFormXs) preFormXs

	val preForm =
	  Vector.mapi
	  (fn (i,(f,fs)) =>
	   let
	     val (f1,fs1) = Vector.sub(preFormXs,i)
	     val (f2,fs2) = Vector.sub(preFormMap,i)
	     val fs =
	       Vector.mapi
	       (fn (j,f) =>
		let
		  val f1 = Vector.sub(fs1,j)
		  val f2 = Vector.sub(fs2,j)
		in
		  (f,f1,f2)
		end) fs
	   in
	     ((f,f1,f2),fs)
	   end) (preForm)

	val target_ys_of_xArr = Array.array (max,nil)

	val (_,doMatch,preForm) = 
	  (* take every regular expression *)
	  Vector.foldli 
	  (fn (re,(_,berry),(off,doMatch,m))
	   => 
	   let 
	     val len = Array.length berry
	     val (F,doMatch,m) = 
	       Array.foldri 
	       (* take every state in the corresponding dfa *)
	       (fn (i,(x,(flw,_,fin,_)),(F,doMatch,m))
		(* x is the label of incoming transitions *)
		(* follow is a list of outgoing transition of form 
		 (where,withWhat)*)
		=> 
		let 
		  (*represent a state by a y*)
		  val y = off+i
		    
		  (* collect info s.t. given a x I have the states
with x as incoming transition *)
		  val _ = (*ys_of_x must be ordered*)
		    if x >= 0 then
		      Array.update 
		      (target_ys_of_xArr,x, y::Array.sub (target_ys_of_xArr,x))
		    else ()
		      
		  (* list of transitions of form (withWhat,where) *) 
		  val trans = Pre.makeTrans (map (fn (j,x) => (x,off+j)) flw)
		    
		  (* list of labels of possible transitions *)
		  val xs = map (fn (x,_) => x) trans
		    
		  (* list of element rules that can be applied for
		   the derivation with one of the outgoing x-s *)
		  val els = List.concat
		    (map (fn x => 
			  let
			       (* the element rules *)
			    val (el,_) = Array.sub(xArr,x)
			  in el end) xs)
		    
		  (* list of text rules that can be applied for
		   the derivation with one of the outgoing x-s *)
		  val txts = List.concat
		    (map (fn x => 
			  let
			    val (_,txt) = Array.sub(xArr,x)
			  in txt end) xs)
		    
		  (* the number of the pattern to which the state y belongs *)
		  val num = if x >=0 then patternNum x else ~1
		    
		  (* info associated with a state *)
		  val _ = Array.update(yArr,y,(re,trans,els,txts,num))

		  val doMatch = Pre.updateTargets (targets,doMatch,x,y)

		  val m = 
		     Pre.mapSpec
		     (fn (a,preFormXs,m) => 
		      (a,preFormXs,
		       (List.foldl
		       (fn (x,m) =>
			let
			  val ys = valOf (IntListMap.find (m,x))
			in
			  IntListMap.insert (m,x,IntLists.addIntList(y,ys))
			end)
			m (IntLists.capIntLists (xs,preFormXs)))))
		     m
		in 
		  (if fin then y::F else F,doMatch,m)
		end)
	       (nil,doMatch,m) berry

	     val _ = Array.update(reArr,re,(off,F))
	   in 
	     (off+len,doMatch,m)
	   end) (0,doMatch,preForm) xreVec

	val reVec = Array.vector reArr

	val y0s_for_ks = Pre.y0s_for_ks (fn re => 
					 let
					   val (y0,_) = Vector.sub(reVec,re)
					 in
					   y0
					 end)
	val _ = Array.modifyi
	  (fn (i,(re,trans,els,txts,num)) => (re,trans,y0s_for_ks els rulArr,txts,num))
	  yArr

	val yVec = Array.vector (yArr)

	val _ = Array.modify (ListMergeSort.sort Int.>) target_ys_of_xArr
	fun target_ys_of_x x= Array.sub (target_ys_of_xArr,x)
	fun re_of_y y = #1 (Vector.sub(yVec,y))
	val ys_of_y = Pre.doYs_of_y 
	  rules target_ys_of_x re_of_y (Vector.length yVec) (Vector.length xreVec)

	val preFormBefore = 
	  Pre.mapSpec
	  (fn (preForm,preFormXs,preFormMap) =>
	   case preForm of
	     NONE => NONE
	   | SOME f =>  
	       SOME 
	       (Formula.mapForm
		(fn x => valOf (IntListMap.find (preFormMap,x))) f))
	  preForm

	val postForm = 
	  Pre.mapSpec
	  (Formula.mapForm target_ys_of_x)
	  preForm1

	val preFormAfterTag = 
	  Pre.mapSpec
	  (fn formula =>
	   (Formula.mapForm
	    (fn x => 
	     let
	       (* element rules by which the x can be derived *)
	      val (els,_) = Array.sub (xArr,x)
		
(* start states for content models which have to be verified for x
(inclusively for negative content models; however, in case of negative
models, the content has to be verified anyway and so probably
couldMatchAfterTag is not used in the matching as the grammar is not
content ignoring) *)

(* negative content models are a separate issue from negative targets;
negative content model have to be verified by the forest automata, as
positive do too; so the corresponding ys have to be(for positive
targets)/shouldn't be(for negative targets) in the state by which the
automaton reaches the beginning of the forest *)
	     in
	       y0s_for_ks els rulArr
	     end) formula))
	  preForm1

	val preFormAfterAtts =
	  Pre.mapSpec
	  (Formula.mapForm
	    (fn x => 
	     let
	       val (els,_) = Array.sub (xArr,x)
	       val ys = y0s_for_ks els rulArr
	       val ys2 = 
		 (* find the variables from which the tree of
		  attributes is to be derived *)
		 case IntListMap.find (xXaXcs,x) of
		   SOME xAxCs =>
		     let
		       val (xAs,_) = ListPair.unzip xAxCs 
			 
(* when specifying the grammar with a pattern, there is always just an
x for attributes; but with a grammar one could say x -> <b k> and x ->
<b l> and therewith more than one types (xs) for the attributes; *)

		       val xAs = rev xAs (* order the xAs *)
			
(* what if some attributes are negated? it's the same as for negative
content models; they have to be checked anyway, so the corresponding
start ys should be in the state *)

(* perform the transition from the ys for the current set of targets
with their types of checked attributes (xAs) *)

		       val yss = 
			 List.map
			 (fn y => (List.concat 
				   (MatchUtil.selectIntList (xAs,#2 (Vector.sub(yVec,y))))))
			 ys
		       val ys4 = List.concat yss
		     in
		       ys4
		     end
		 | NONE => nil 			
(* as x, the target is not an element and the computed list is not
used anyway *)

	     in
	       sortInt ys2
	     end))
	  preForm1
	  	      
      in
	(yVec,reVec,doMatch,ys_of_y,preFormBefore,preFormAfterTag,preFormAfterAtts,postForm)
      end

    
    (*--------------------------------------------------------------*)
    (* q0 = {y_(0,j)| ...&& _ re_j&&... in E0                       *)
    (*--------------------------------------------------------------*)
    fun doQ0 starts y0_of_re =
      foldr 
      (fn (fe,y0s) => foldr 
       (fn ((_,re),y0s) => addIntList(y0_of_re re,y0s)) 
       y0s fe)
      nil starts


    fun alg patternNum (((max,starts,rules),
			 xreVec,tpVec,qualifiersInfo),matchSpecs) =
      let
	val (xArr,rulArr) = Pre.doXVec (max,rules)
	val (yVec,reVec,doMatch,ys_of_y,
	     preForm,preFormAfterTag,preFormAfterAtts,postForm) = 
	  doYVec (max,xArr,rulArr,xreVec,patternNum,rules,qualifiersInfo,matchSpecs)
	fun y0_of_re re = #1 (Vector.sub (reVec,re))
	fun F_of_re re = #2 (Vector.sub (reVec,re))
	fun F1_of_re re = nil
	val (sigVec,rhsVec,otherRules,otherY0s,regexpNameRules) =
	  Pre.doRest (starts,rulArr,xArr,y0_of_re,F_of_re,F1_of_re)
	val q0 = doQ0 starts y0_of_re	  
      in
	(yVec,sigVec,rhsVec,tpVec,otherRules,
	 otherY0s,q0,doMatch,ys_of_y,regexpNameRules,
	 preForm,preFormAfterTag,preFormAfterAtts,postForm)
      end

    fun multPreAlg intervals (flat as ((max,_,_),_,_,_),matchSpecs) =
      let
	(*-----------------------------------------------------------*)
	(* holds for each x whether it is a target and the number of *)
	(* the pattern it belongs to.                                *)
	(*-----------------------------------------------------------*)
	val xTemp = Array.array (max,(false,~1))
	(* enter the pattern numbers *)
	val _ = Vector.appi 
	  (fn (i,interval) => appInterval (fn x => Array.update(xTemp,x,(false,i))) 
	   interval) intervals
	fun patternNum x = #2(Array.sub(xTemp,x))
      in 
	alg patternNum (flat,Vector.fromList matchSpecs)
      end

    fun preAlg (flat as ((max,_,_),_,_,_),matchSpec) =
      let
	fun patternNum x = 0
	val pre as (yVec,sigVec,rhsVec,tpVec,otherRules,
	     otherY0s,q0,doMatch,ys_of_y,regexpNameRules,
	     preForm,preFormAfterTag,preFormAfterAtts,postForm) =
	  alg patternNum (flat,#[matchSpec])
	  
	val _ = 
	(*---------------------------------------------------*)
	(* possibly do some debugging output                 *)
	(*---------------------------------------------------*)
	if !O_GREP_DEBUG<=1 then ()
	else let val Int2String = (StringCvt.padLeft #" " 6) o Int.toString
	     in app print
	       ["Single Pass:\n  ",
		Int2String (Vector.length sigVec)," element types\n  ",
		Int2String max," tree variables\n  ",
		Int2String (Vector.length yVec)," nfa states\n  ",
		Int2String (Vector.length rhsVec)," rules\n  ",
		Int2String (Vector.length tpVec)," text patterns\n  ",
		Int2String (length q0)," initial dfa states\n\n."]
	     end
      in
	pre
      end
  end
