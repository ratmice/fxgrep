structure Pre =
  struct
    open GramData GramUtil IntLists UtilInt

    val THIS_MODULE = "Pre"

    type RhsVector = (int * (int list list * int list * int list * int list list) * int option) vector
    type AVector = (int list * int list) vector  
    type TextPatternsVector = TextDfa.Dfa vector 
    type OtherRules = int list
    type OtherY0s = int list
    type Primaries = IntLists.IntList 
    type Secondaries = IntLists.IntList vector
    type DoMatch = Primaries * Secondaries
    type YsFormula = IntLists.IntList Formula.Formula
    type 'a Spec = ('a * 'a vector) vector


(* for secondary targets *)
    type RegExpNamesInfo = (int * TextDfa.Dfa * int list) list
    type Intervals = (int * int) vector

(* ys on the parent level of some y *)
    type YTargetsVector = int list vector


    fun mapSpec f form = 
      Vector.map 
      (fn (preForm1,preForm2) => (f preForm1, Vector.map f preForm2))
      form

    fun initTargets matchSpecs = 
      let
	val targets =
	  Vector.map
	  (fn ((form1,t1),t') => 
	   (t1, Vector.fromList (List.map (fn (form2,t') => t') t')))
	  matchSpecs


	val doMatch = 
	  Vector.map
	  (fn (targets,targets') =>
	   (IntLists.emptyIntList,
	    Vector.map (fn t => IntLists.emptyIntList) targets')) targets

	val preForm =
	  Vector.map 
	  (fn ((form1,targets1),secondaries) => 
	   (form1, Vector.fromList (List.map (fn (form2,targets2) => form2) secondaries)))
	  matchSpecs

      in
	(targets,doMatch,preForm)
      end

    fun updateTargets (targets,doMatch,x,y) =
      Vector.mapi 
      (fn (i,(targets,targets')) =>
       let
	 val (doYs,doYss') = Vector.sub (doMatch,i)
       in
	 (if inIntList (x,targets) then IntLists.addIntList(y,doYs) else doYs,
	    Vector.mapi 
	    (fn (i,targets') =>
	     let
	       val doYs' = Vector.sub(doYss',i)
	     in
	       if inIntList (x,targets') then IntLists.addIntList(y,doYs') else doYs'
	     end)
	    (targets',0,NONE))
       end) (targets,0,NONE)



    (*--------------------------------------------------------------*)
    (* xVec[y] = ({k|Rules[k]=x->_<e_k>},                           *)
    (*            {k|Rules[k]=x->"..."})                            *)
    (*--------------------------------------------------------------*)
    fun doXVec (max,rules) =
      let
	val numRules = foldr (fn ((_,rhss),num) => num+length rhss) 0 rules
	val xArr = Array.array (max,(nil,nil))
	val rulArr = Array.array (numRules,(0,GramData.FLAT_TEXT NONE))

	  
	(* there is just one rule per x; the rhss are
	 right-hand-sides of rules in which x is on the lhs *)
	val _ = 
	  (* for every x *)
	  foldl 
	  (fn ((x,rhss),idx) 
	   => let 
		val (els,txts,idx1) = 
		  (* for every right hand side *)
		  foldl
		  (fn (rhs,(els,txts,idx))
		   => 
		   (* remember the element rhss, and the element rhss
		   for a given x, in two lists of indices standing for
		   the right-hand side for each x *)
		   (case rhs of 
		      GramData.FLAT_ELEM _ => (idx::els,txts,idx+1)
		    | GramData.FLAT_TEXT tp => (els,idx::txts,idx+1))
		   before Array.update(rulArr,idx,(x,rhs)))
		  (nil,nil,idx) rhss
		val _ = Array.update(xArr,x,(rev els,rev txts))
	      in idx1
	      end
	    ) 0 rules
      in 
	(xArr,rulArr)
      end
    
    fun y0s_for_ks y0_of_re ks rulArr = 
      (* rulArr stores the information for rules *)
      (* ks denotes a set of rules *)
      (* y0_of_re a function that given a regular expression returns
      the start state of the corresponding dfa *)
      sortInt
      (foldl (fn (k,y0s) => 
	      case Array.sub (rulArr,k) of 
		(_,FLAT_TEXT _) => y0s
	      | (_,FLAT_ELEM(_,fe)) => 
		  (* a forest expression is a conjunction of possibly
		  negated regular expression; collect the start states
		  of each re *)
		  foldr (fn ((_,re),y0s) => (y0_of_re re)::y0s) y0s fe) nil ks)

    fun makeTrans nil = nil
      | makeTrans (xys as ((x,_)::_)) = 
      let 
	val m = foldr (fn ((x,y),m) => Int.min(x,m)) x xys 
	val (these,those) = List.partition (fn (x,y) => x=m) xys
      in 
	(m,map #2 these)::makeTrans those
      end
    
            
    fun doRest (starts,rulArr,xArr,y0_of_re,F_of_re,F1_of_re) =
      let
	(*--------------------------------------------------------------*)
	(* compute the set of symbols occurring in G                    *)
	(*--------------------------------------------------------------*)
	val sigma = sortInt 
	  (Array.foldl 
	   (fn ((_,rhs),sigma) 
	    => case rhs 
	    of FLAT_TEXT _ => sigma
	  | FLAT_ELEM(gp,_) => case gp
	      of GI_POS gis => cupIntLists (sigma,gis)
	    | GI_NEG gis => cupIntLists (sigma,gis)
	    | GI_REG _ => sigma)
	   nil rulArr)

	  
	(*--------------------------------------------------------------*)
	(* sigVec[a] = ({k|Rules[k]=_->a<e_k>},                         *)
	(*              {y_{0,j)|_->a<... && _ re_j _ && ...>}          *)
	(*--------------------------------------------------------------*)
	 local
	   val sigArr = Array.array(List.last sigma+1,nil)
	     
	   val (otherRules,regexpNameRules) = Array.foldri
	     (fn (rul,(_,rhs),(others,regexpNameRules)) 
	      => case rhs 
	      of FLAT_TEXT _ => (others,regexpNameRules)
	    | FLAT_ELEM(gp,fe) => 
		case gp
		  of GI_POS gis => (others,regexpNameRules) before app 
		    (fn a => Array.update(sigArr,a,rul::Array.sub(sigArr,a))) 
		    gis
		  | GI_NEG ngis => 
		    let val _ = app 
		      (fn a => Array.update(sigArr,a,rul::Array.sub(sigArr,a))) 
		      (diffIntLists(sigma,ngis))
		    in 
		      (rul::others,regexpNameRules)
		    end
	          | GI_REG tp => 
		    let 
		      val dfa = TextDfa.makeDfa tp
		      val y0s = List.foldr 
			(fn ((sign,re),y0s) => (y0_of_re re)::y0s) nil fe
		    in
		      (others,(rul,dfa,y0s)::regexpNameRules)
		    end
		  ) (nil,nil) (rulArr,0,NONE) 

	   val y0s_for_ks = y0s_for_ks y0_of_re
	     
	   val otherY0s = y0s_for_ks otherRules rulArr
	     
	   val sigVec = Vector.tabulate 
	     (Array.length sigArr,
	      fn a => if inIntList(a,sigma) 
			then let val rules = Array.sub(sigArr,a)
			     in (rules,y0s_for_ks rules rulArr)
			     end 
		      else (otherRules,otherY0s))
	 in 
	   val (sigVec,regexpNameRules,otherRules,otherY0s) = 
	     (sigVec,regexpNameRules,otherRules,otherY0s)
	 end

	(*--------------------------------------------------------------*)
	(* rhsVec[k] = (x^k,                                            *)
	(*              {F_j|Rules[k]=x->_<...&& +re_j &&...>},         *)
	(*              {y|y in F_j, Rules[k]=x->_<...&& -re_j &&...>}, *)
	(*              tp with Rules[k]=x->"tp")                       *)
	(*--------------------------------------------------------------*)
	 val rhsVec =
	   Vector.tabulate
	   (Array.length rulArr, 
	    fn k => case Array.sub(rulArr,k)
	    of (x,FLAT_TEXT tp) => (x,(nil,nil,nil,nil),tp)
	  | (x,FLAT_ELEM(_,fe)) => foldr
	      (fn ((sign,re),(x,(posFs,negF,posF,posFs1),tp)) 
	       =>
	       let
		 val F = F_of_re re
		 val F1 = F1_of_re re
	       in
		 if sign then (x,(F::posFs,negF,cupIntLists(F,posF),F1::posFs1),tp) 
		 else (x,(posFs,cupIntLists(F,negF),posF,posFs1),tp)
	       end)		   
	      (x,(nil,nil,nil,nil),NONE) fe)

      in
	(sigVec,rhsVec,otherRules,otherY0s,regexpNameRules)
      end

    fun doYs_of_y rules target_ys_of_x re_of_y yVecLength xreVecLength =
      (* re_of_y has for a y the re in which it occurs *)
      let
	(* x_of_re will collect for every regular expression the x on
	the left side of the rule in which that re occurs *)
	val x_of_re = 
	  let 
	    val arr = Array.array (xreVecLength,NONE)
	    fun addX x re = 
	      case Array.sub (arr,re) of 
		NONE => Array.update(arr,re,SOME x)
	      | _ => raise UtilError.InternalError 
		  (THIS_MODULE,"analyze",
		   "regular expression shared among x-s")
	    val _ = app 
	      (fn (x,rhss) => app 
	       (fn rhs => 
		case rhs of 
		  FLAT_TEXT _ => ()
		| FLAT_ELEM(_,fe) => app (fn (_,re) => addX x re) fe)
	       rhss)
	      rules
	  in 
	    Array.extract (arr,0,NONE)
	  end

        (* given a y, it returns the list of posible ys in the output
        state of the parent level *)

	val ys_of_y = Vector.tabulate 
	  (yVecLength, fn y => 
	   case Vector.sub (x_of_re,re_of_y y) of
	     SOME x1 => target_ys_of_x x1
	   | NONE => nil 
      (* y is in the dfa of the start expression; there is nothing to
      carry to the parent level as there is no parent level, the list
      is then nil *)
	       )

      in
	ys_of_y
      end

  end
