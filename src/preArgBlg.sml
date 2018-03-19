signature PreArgBlg =
  sig
    type Ql0Info = (int list list * int list * int list) list
      
    type YVector = (int * (int * int list) list * int list * int list 
		    * (int * int list) list * int list * int) vector
    type IncomingXVector = int vector
    type PreArgBlg = 
      (Pre.AVector * YVector * Pre.RhsVector * Pre.TextPatternsVector 
       * Pre.OtherRules * Pre.OtherY0s * int list * Ql0Info * 
       Pre.DoMatch vector * IncomingXVector * Pre.RegExpNamesInfo * 
       Pre.YTargetsVector * Pre.YsFormula Pre.Spec)
    val multPreArgBlg : Pre.Intervals -> GramFlatten.Flat * GramData.MatchSpec list -> (*Mult*)PreArgBlg
    val preArgBlg : GramFlatten.Flat * GramData.MatchSpec -> PreArgBlg
  end

structure PreArgBlg : PreArgBlg =
  struct
    open GramData GramTables GramUtil GrepOptions IntLists UtilInt
      
    val THIS_MODULE = "PreArgBlg"

    type Ql0Info = (int list list * int list * int list) list

    type YVector = (int * (int * int list) list * int list * int list 
		    * (int * int list) list * int list * int) vector
    type IncomingXVector = int vector
    type YTargetsVector = int list option vector
    type PreArgBlg = 
      (Pre.AVector * YVector * Pre.RhsVector * Pre.TextPatternsVector * 
       Pre.OtherRules * Pre.OtherY0s * int list * Ql0Info * 
       Pre.DoMatch vector * 
       IncomingXVector * Pre.RegExpNamesInfo * Pre.YTargetsVector * Pre.YsFormula Pre.Spec)

    (*--------------------------------------------------------------*)
    (* yVec[y] = ({(x,y1)|(y,x,y1)in delta_j})                      *)
    (*            {y_(0,j)|(y,x,y1)in delta_j,                      *)
    (*                     Rules[k]=x-><... && _ re_j && ...>},     *)
    (*            {k|(y,x,y1)in delta_j,Rules[k]=x->"..."},         *)
    (*            {(x,y1)|(y1,x,y)in delta_j},                      *)
    (*            {y_F|y in F_j, (y1,x,y)in delta_j,                *)
    (*                 Rules[k]=x-><... && + re_j && ...>})         *)
    (*--------------------------------------------------------------*)
    (* first int in yVec[y] = mapping from y to re *)
    fun doYVec (xreVec,max,xArr,rulArr,matchSpecs,patternNum,rules) =
      let
	val numY = Vector.foldl (fn ((_,berry),num) => num+Array.length berry) 0 xreVec
	val yArr = Array.array (numY,(~1,nil,nil,nil,nil,nil,~1))
	val reArr = Array.array (Vector.length xreVec,((0,0),nil,nil))

	val target_ys_of_xArr = Array.array (max,nil)
	val incoming_x_of_yArr = Array.array (numY,~1)
				       
	val (targets,doMatch,preForm) = Pre.initTargets matchSpecs

	fun makeTrans nil = nil
	  | makeTrans (xys as ((x,_)::_)) = 
	  let 
	    val m = foldr (fn ((x,y),m) => Int.min(x,m)) x xys 
	    val (these,those) = List.partition (fn (x,y) => x=m) xys
	  in 
	    (m,map #2 these)::makeTrans those
	  end

	val (_,allTrans,doMatch) = Vector.foldli 
	  (fn (re,(_,berry),(off,allTrans,doMatch))
	   (*off is the number assigned to first state in the
	    current NFA, i.e. its start state*)
	   => 
	   let 
	     val len = Array.length berry
	     val (F,F1,allTrans1,doMatch) = Array.foldri 
	       (fn (i,(x,(flw,prc,final,ini)),(F,F1,allTrans,doMatch)) 
		=> let
		     val y = off+i
		     val _ = Array.update 
		       (incoming_x_of_yArr,y,x)
		     val _ = 
		       (*ys_of_x must be ordered*)
		       if x >= 0 then
			 Array.update 
			 (target_ys_of_xArr,x,
			  y::Array.sub (target_ys_of_xArr,x))
		       else ()
		     val xy1s = map (fn (j,x) => 
				     (x,off+j)) prc
		     (*xy1s are y1 states preceding y and having incoming x*)
		     val trans = makeTrans xy1s
		     (*shorten representations of xy1s, where
		      ys having the same incoming x are put
		      together in a list ordered after x*)
		     val allTrans1 = map 
		       (fn (x,y1) => (y1,x,y)) xy1s@allTrans
		     val xs = map #1 trans (*incoming xs of preceding y1s*)
		     val els = List.concat
		       (map (fn x => #1(Array.sub(xArr,x))) xs)
		     (*order number of element rules having on the left hand side xs*)
		     val txts = List.concat
		       (map (fn x => #2(Array.sub(xArr,x))) xs)
		     val num = if x>= 0 then patternNum x
			       else ~1
		     val _ = Array.update(yArr,y,(re,trans,els,txts,nil,nil,num))
		       
		  val doMatch = Pre.updateTargets (targets,doMatch,x,y)		    
		   in 
		     (if ini then y::F else F, if final then y::F1 else F1,allTrans1,doMatch)
		   end)
	       (nil,nil,allTrans,doMatch) (berry,0,NONE) 
	     val _ = Array.update(reArr,re,((off,off+len),F,F1))
	   in 
	     (off+len,allTrans1,doMatch)
	   end) 
	  (0,nil,doMatch) (xreVec,0,NONE)
		 
	fun makeRTrans nil = ()
	  | makeRTrans (y1xys as ((y1,_,_)::_)) = 
	  let 
	    val m = foldr (fn ((y1,_,_),m) => Int.min(y1,m)) y1 y1xys 
	    val (these,those) = List.partition (fn (y1,_,_) => y1=m) y1xys
	    val xys = sortIntPair 
	      (map (fn (y1,x,y) => (x,y)) these)
	    val trans = makeTrans xys
	    val xs = map #1 trans
	    val els = List.concat
	      (map (fn x => 
		    let
		      val (els,txts) = Array.sub(xArr,x)
		    in
		      els
		    end) xs)
	    val (a,b,c,d,_,_,num) = Array.sub(yArr,m)
	    val _ = Array.update(yArr,m,(a,b,c,d,trans,els,num))
	  in 
	    makeRTrans those
	  end
	
	val _ = makeRTrans allTrans
	  
	fun y0s_for_ks ks = sortInt (*initial states for the rules ks*)
	  (foldl (fn (k,y0s) => 
		  let
		    val (x,rhs) = Array.sub(rulArr,k)
		  in
		  case rhs of 
		    FLAT_TEXT _ => y0s
		  | FLAT_ELEM(_,fe) => foldr
		      (fn ((_,re),y0s) => 
		       (let
			 val ((ini,last),F,F1) = Array.sub(reArr,re)
		       in
			 ini
		       end)::y0s) y0s fe
		  end) nil ks)
	  
	fun yFs_for_ks ks = sortInt
	  (foldl (fn (k,y0s) => 
		  let
		    val (x,rhs) = Array.sub(rulArr,k)
		  in
		  case rhs of 
		    FLAT_TEXT _ => y0s
		  | FLAT_ELEM(_,fe) => foldr
		      (fn ((sign,re),y0s) 
		       => if sign then 
		       let
			 val ((ini,last),F,F1) = Array.sub(reArr,re)
		       in
			 F@y0s 
		       end
			  else y0s) y0s fe
		  end) nil ks)
	  
	val _ = Array.modifyi
	  (fn (i,(re,trans,els,txts,transR,elsR,num)) 
	   => (re,trans,y0s_for_ks els,
	       (*will be used in the right-to-left automaton to
		compute the initial rightmost forest state when
		executing a down transition; the trick is to begin
                with forest state, whose reverse transitions (as
		constructed in the prec of the NFA) lead to final
	        states*)
	       txts,transR,yFs_for_ks elsR,num))
	  (yArr,0,NONE)
	val y0s_for_ks = y0s_for_ks 


	val (incomingXVec,yVec,reVec) = 
	  (Array.extract(incoming_x_of_yArr,0,NONE),
	   Array.extract(yArr,0,NONE),
	   Array.extract (reArr,0,NONE))

	val _ = Array.modify (ListMergeSort.sort Int.>) target_ys_of_xArr
	fun target_ys_of_x x= Array.sub (target_ys_of_xArr,x)
	fun re_of_y y = #1 (Vector.sub(yVec,y))
	val ys_of_y = Pre.doYs_of_y 
	  rules target_ys_of_x re_of_y (Vector.length yVec) (Vector.length xreVec)
	val form = 
	  Pre.mapSpec
	  (Formula.mapForm target_ys_of_x)
	  preForm
      in
	(y0s_for_ks,ys_of_y,incomingXVec,yVec,reVec,doMatch,form)
      end

    (*--------------------------------------------------------------*)
    (* qr0 = {y_(0,j)| ...&& _ re_j&&... in E0                      *)
    (*--------------------------------------------------------------*)
    fun doInitialStates starts y0_of_re F_of_re =
      foldr 
      (fn (fe,(y0s,ql0info)) => 
       let 
	 val (y0s1,posFs,negF,posF) = foldr 
	   (fn ((sign,re),(y0s,posFs,negF,posF)) => 
	    let 
	      val y0 = y0_of_re re
	      val F = F_of_re re
	      val y0s1 = addIntList(y0,y0s)
	      val (posFs1,negF1,posF1) = 
		if sign then (F::posFs,negF,cupIntLists(F,posF))
		else (posFs,cupIntLists(F,negF),posF)
	    in 
	      (y0s1,posFs1,negF1,posF1)
	    end)
	   (y0s,nil,nil,nil) fe
       in 
	 (y0s1,(posFs,negF,posF)::ql0info)
       end)
      (nil,nil) starts


    fun argBlg patternNum (((max,starts,rules),
			    xreVec,tpVec,qualifiers),matchSpecs) =
      let
	val (xArr,rulArr) = Pre.doXVec (max,rules)
	val (_,ys_of_y,incomingXVec,yVec,reVec,doMatch,form)
	  = doYVec (xreVec,max,xArr,rulArr,matchSpecs,patternNum,rules)
	fun y0_of_re re = let val ((off,offPlusLen),F,F1) = Vector.sub (reVec,re) in off end
	fun F_of_re re = let val ((off,offPlusLen),F,F1) = Vector.sub (reVec,re) in F end
	fun F1_of_re re = let val ((off,offPlusLen),F,F1) = Vector.sub (reVec,re) in F1 end
	val (sigVec,rhsVec,otherRules,otherY0s,regExpNameRules) =
	  Pre.doRest (starts,rulArr,xArr,y0_of_re,F_of_re,F1_of_re)
	val (qr0,ql0info) = doInitialStates starts y0_of_re F_of_re

	(*---------------------------------------------------*)
	(* possibly do some debugging output                 *)
	(*---------------------------------------------------*)
	val _ = if !O_GREP_DEBUG<=1 then ()
                    else let val Int2String = (StringCvt.padLeft #" " 6) o Int.toString
                         in app print
                            ["Two Passes:\n  ",
                             Int2String (Vector.length sigVec)," element types\n  ",
                             Int2String (Array.length xArr)," tree variables\n  ",
                             Int2String (Vector.length yVec)," nfa states\n  ",
                             Int2String (Vector.length rhsVec)," rules\n  ",
                             Int2String (Vector.length tpVec)," text patterns\n  ",
                             Int2String (length qr0)," initial dfa states\n  "(*,
                             Int2String (length doMatch)," matching dfa states\n\n"*)]
			 end

      in 
	(sigVec,yVec,rhsVec,tpVec,otherRules,
	 otherY0s,qr0,ql0info,doMatch,
	 incomingXVec,regExpNameRules,ys_of_y,form)
	 
      end

    fun multPreArgBlg intervals (flat as ((max,_,_),_,_,_),matchSpecs) =
      let
	(*-----------------------------------------------------------*)
	(* holds for each x whether it is a target and the number of *)
	(* the pattern it belongs to.                                *)
	(*-----------------------------------------------------------*)
	val xTemp = Array.array(max,(false,~1))
	val _ = Vector.appi 
	  (fn (i,interval) => appInterval (fn x => Array.update(xTemp,x,(false,i))) 
	   interval) (intervals,0,NONE)
	fun numOf x = #2(Array.sub(xTemp,x))
	val patternNum = numOf
      in 
	argBlg patternNum (flat,Vector.fromList matchSpecs)
      end


    fun preArgBlg (flat,matchSpec) =
      let
	fun patternNum x = 0
      in
	argBlg patternNum (flat,#[matchSpec])
      end

   end
