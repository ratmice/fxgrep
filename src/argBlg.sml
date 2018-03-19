structure ArgBlg = 
  struct
    open DocDtd Errors IntLists MatchData MatchUtil GrepOptions MatchOptions

    fun argBlg
      (sigVec,yVec,rhsVec,tpVec,
       otherRules,otherY0s,qr0,ql0info,
       incomingXVec,regExpNameRules,target_ys_of_x) dtd =
      let	
	fun rules_for_a a = 
	  let
	    val (v,_) =  Vector.sub(sigVec,a)
	  in
	    v
	  end 
	handle Subscript => otherRules

	fun y0s_for_a a = #2(Vector.sub(sigVec,a)) handle Subscript => otherY0s
	fun x_of_rule rule = let val (x,_,_) = Vector.sub(rhsVec,rule) in x end
	fun Fs_for_rule rule = let val (_,Fs,_) = Vector.sub(rhsVec,rule) in Fs end

	val O_TS_MATCH = ref 5

	val printout = ignore
	val printout1 = ignore

	val pDict = IntListDict.makeDict ("tree state",!O_TS_MATCH,(nil,NONE))
	val qDict = IntListDict.makeDict ("forest state",!O_TS_MATCH, (NONE,NONE,NONE,NONE))
	val elDict = IntDict.makeDict ("element names and nfa-s",!O_TS_MATCH,(nil,nil))
	val intersectionDict = IntPairDict.makeDict ("intersection",!O_TS_MATCH,0)
	    
	fun elDictLookup a =
	  case IntDict.hasIndex(elDict,a) of
	    SOME i => IntDict.getByIndex (elDict,i)
	  | NONE => 
	      let
		val elementName = UniChar.Data2Vector (DocDtd.Index2Element dtd a)
		val res as (y0s_regExpRules,regExpRules) =
		  List.foldl 
		  (fn ((rul,dfa,y0s),(y0sAcc,rules)) =>
		   if (TextDfa.runDfas [(0,dfa)] elementName)=[0]
		     then (cupIntLists (y0s,y0sAcc),rul::rules)
		   else (y0sAcc,rules)) (nil,nil) regExpNameRules
	      in
		res before IntDict.setByKey(elDict,a,res)
	      end

	fun getPstate i = IntListDict.getKey(pDict,i)
	fun getPindex ks = 
	  case IntListDict.hasIndex(pDict,ks)
	    of SOME i => i
	  | NONE => let val xs = sortInt (map x_of_rule ks)
			val i = IntListDict.getIndex(pDict,ks)
		    in i before IntListDict.setByIndex(pDict,i,(xs,NONE)) 
		    end
	fun getPinfo i = IntListDict.getByIndex(pDict,i)
	fun setPinfo(i,x) = IntListDict.setByIndex(pDict,i,x)
	val xs_of_p = #1 o getPinfo 

	fun getQstate i = IntListDict.getKey(qDict,i)
	fun getQindex q = IntListDict.getIndex(qDict,q)
	fun getQinfo i = IntListDict.getByIndex(qDict,i)
	fun setQinfo(i,x) = IntListDict.setByIndex(qDict,i,x)

	fun getIntersection (q,qr) =
	  case IntPairDict.hasIndex (intersectionDict,(q,qr)) of
	    SOME i => IntPairDict.getByIndex (intersectionDict,i)
	  | NONE => 
	      let
		val qq = getQindex (capIntLists (getQstate q,getQstate qr))
	      in
		qq before IntPairDict.setByKey (intersectionDict,(q,qr),qq)
	      end


	local 
	  fun trans_for_y y = let val (_,trans,_,_,_,_,_) = Vector.sub(yVec,y) in trans end
	  fun y0s_for_y y = let val (_,_,y0s,_,_,_,_) = Vector.sub(yVec,y) in y0s end
	  fun txt_rules_for_y y = let val (_,_,_,rules,_,_,_) = Vector.sub(yVec,y) 
				  in rules end
				
	  fun tp_for_rule rule = let val (_,_,tp) = Vector.sub(rhsVec,rule) in (rule,tp) end
	  fun dfa_for_tp tp = (tp,Vector.sub(tpVec,tp))
	    
	  val downDict = IntPairDict.makeDict ("down transition",!O_TS_MATCH,0)
	  val upDict = IntPairDict.makeDict ("up transition",!O_TS_MATCH,0)
	  val tupDict = IntIntListDict.makeDict ("text up transition",!O_TS_MATCH,0)
	  val sideDict = IntPairDict.makeDict ("side transition",!O_TS_MATCH,0)

	  fun hasTransition dict pair = 
	    case IntPairDict.hasIndex(dict,pair) 
	      of NONE => NONE
	    | SOME i => SOME (IntPairDict.getByIndex(dict,i))
	  fun setTransition dict (pair,res) = IntPairDict.setByKey(dict,pair,res)
		  
	  val hasUp = hasTransition upDict
	  val hasDown = hasTransition downDict
	  val hasSide = hasTransition sideDict
	  val setUp = setTransition upDict
	  val setDown = setTransition downDict
	  val setSide = setTransition sideDict
		  
	  (*--------------------------------------------------------------*)
	  (* y0s_for_q q = { y_(0,j) | y in q, (y,x,_)in delta,           *)
	  (*                           x -> _<... && _ re_j && ...> }     *)
	  (*--------------------------------------------------------------*)
	  fun y0s_for_q q =
	    case getQinfo q 
	      of (SOME a,_,_,_) => a
	    | (NONE,b,c,d) => let val ys = getQstate q
				val a = foldl 
				  (fn (y,y0s) => cupIntLists(y0s_for_y y,y0s)) nil ys
			    in a before setQinfo(q,(SOME a,b,c,d))
			    end
				  
	  (*--------------------------------------------------------------*)
	  (* txt_rules_for_q q = { k | y in q, (y,x,y_1)in delta,         *)
	  (*                           rules[k] = x -> "_" }              *)
	  (* return { (k,tp) | rules[k] = _ -> "tp" }                     *)
	  (*    and { (tp,dfa) | rules[k] = _ -> "tp", k in txt_rules }   *)
	  (*--------------------------------------------------------------*)
	  fun txt_rules_for_q q =
	    case getQinfo q 
	      of (_,SOME b,_,_) => b
	    | (a,NONE,c,d) => let val ys = getQstate q
				val rules = foldl 
				  (fn (y,ks) => cupIntLists(txt_rules_for_y y,ks)) nil ys
				val ktps = map tp_for_rule rules
				val tps = sortInt (List.mapPartial #2 ktps)
				val dfas = map dfa_for_tp tps
				val b = (ktps,dfas)
			    in b before setQinfo(q,(a,SOME b,c,d))
			    end
				  
	  (*--------------------------------------------------------------*)
	  (* down a q = {y_{0,j} | y in q, (y,x,y_1) in delta,            *)
	  (*                       x -> a<...&& _ re_j &&...> }           *)
	  (*--------------------------------------------------------------*)
	  fun down(a,q) = 
	    case hasDown(a,q)
	      of SOME q0 => q0
	    | NONE => let val y0s = capIntLists (y0s_for_a a,y0s_for_q q)
			  val q0 = getQindex y0s
		      in q0 before setDown((a,q),q0)
		      end
	  fun downRegExpNames (a,q,y0s_regExpRules) = 
	    case hasDown(a,q)
	      of SOME q0 => q0
	    | NONE => 
		let 
		  val y0s = capIntLists
		    (cupIntLists (y0s_for_a a,y0s_regExpRules),
		     y0s_for_q q)
		  val q0 = getQindex y0s
		in 
		  q0 before setDown((a,q),q0)
		end

	  (*--------------------------------------------------------------*)
	  (* up a q = {k | rules[k]= _ -> a<e_k>,                         *)
	  (*               q cap F_j <> 0 for e_k = ...&& +re_j &&...,    *)
	  (*               q cap F_j =  0 for e_k = ...&& -re_j &&... }   *)
	  (*--------------------------------------------------------------*)
	  fun up(a,q) = 
	    case hasUp(a,q) 
	      of SOME p => p
	    | NONE => let val ys = getQstate q
			  val ks = List.filter 
			    (fn rule => 
			     let val (posFs,negFs,_,posF1) = Fs_for_rule rule
			     in if capIntLists(ys,negFs)<>nil then false
				else List.all 
				  (fn posF => capIntLists(ys,posF)<>nil) posFs
			     end) (rules_for_a a)
			  val p = getPindex ks
		      in 
			p before setUp ((a,q),p)
		      end
	  fun upRegExpNames (a,q,regExpRules) = 
	    case hasUp(a,q) 
	      of SOME p => p
	    | NONE => 
		let 
		  val ys = getQstate q
		  fun filterRule rule = 
		    let 
		      val (posFs,negFs,_,_) = Fs_for_rule rule
		    in 
		      if capIntLists(ys,negFs)<>nil then false
		      else List.all (fn posF => capIntLists(ys,posF)<>nil) posFs
		    end
		  val ks = List.filter filterRule (rules_for_a a)
		  val ks_regExp = List.filter filterRule regExpRules
		  val ks = cupIntLists (ks,rev ks_regExp)
		  val p = getPindex ks
		in 
		  p before setUp ((a,q),p)
		end
			    
	  (*--------------------------------------------------------------*)
	  (* assure that txt_rules_for q = (ktps,_). Then                 *)
	  (* txt_up q matches = { k | (k,tp) in ktps, tp in matches }.    *)
	  (*--------------------------------------------------------------*)
	  fun txt_up(q,ktps,matches) = 
	    case IntIntListDict.hasIndex(tupDict,(q,matches))
	      of SOME i => IntIntListDict.getByIndex(tupDict,i)
	    | NONE => let
			val ks = List.mapPartial 
			  (fn (k,tp) => 
			   case tp 
			     of NONE => SOME k
			   | SOME i => if inIntList(i,matches) 
					 then SOME k else NONE) 
			  ktps 
			val p = getPindex ks
		      in 
			p before IntIntListDict.setByKey(tupDict,(q,matches),p)
		      end
			    
	  (*--------------------------------------------------------------*)
	  (* side q p = { y | y1 in q, k in p, (y,x^k,y1)in delta }       *)
	  (*--------------------------------------------------------------*)
	  (* the side transitions of the right-to-left automaton          *)
	  (* follow the transitions of the finite automata in             *) 
	  (* reverse. It beginns however with the initial state of        *) 
	  (* the NFA-s, and the first step backward is made to the        *)
	  (* final states. In this way the output state of side           *) 
	  (* transition is a superset of the NFA states reached by        *)
	  (* the NFAs AFTER seeing the node for which the side            *)
	  (* transition is executed                                       *)
	  (*--------------------------------------------------------------*)
	  fun side(q,p) =
	    case hasSide(q,p)
	      of SOME q1 => q1
	    | NONE => let val ys = getQstate q
			  val xs = xs_of_p p
			  val y1ss = map 
			    (fn y => let val trans = trans_for_y y
				     in List.concat (selectIntList (xs,trans))
				     end)
			    ys
			  val y1s = sortInt (List.concat y1ss)
			  val q1 = getQindex y1s
		      in q1 before setSide((q,p),q1)
		      end
			    
	  (*--------------------------------------------------------------*)
	  (* text q txt = { k | y in q, (y,x,y_1)in delta,                *)
	  (*                    rules[k] = x -> "tp", txt match tp. }     *)
	  (*--------------------------------------------------------------*)
	  fun text(q,txt) = 
	    let 
	      val (ktps,dfas) = txt_rules_for_q q
	      val matches = TextDfa.runDfas dfas txt
	    in txt_up(q,ktps,matches)
	    end


	  fun doText q txt = (text(q,txt),0,0,0,emptyLabeling)
	  fun doPi q (target,cont) deltaF deltaA =
	    let 
	      val q0 = down(piIdx,q)
	      val qc0 = down(contentIdx,q0)
	      val (lsc,qc1) = deltaF(qc0,cont)
	      val pc = up(contentIdx,qc1)
	      val q1 = side(q0,pc)
	      val qa0 = down(attrsIdx,q1)
	      val qa1 = deltaA(qa0,Vector.fromList[(targetIdxE,target)])
	      val pa = up(attrsIdx,qa1)
	      val q2 = side(q1,pa)
	    in 
	      (up(piIdx,q2),pa,q1,pc,lsc)
	    end
	  fun doElem q (a,atts,cont) deltaF deltaA =
	    let 
	      val (y0s_regExpRules,regExpRules) = elDictLookup a
	      val q0 = downRegExpNames(a,q,y0s_regExpRules)
	      val qc0 = down(contentIdx,q0)
	      val (lsc,qc1) = deltaF(qc0,cont)
	      val pc = up(contentIdx,qc1)
	      val q1 = side(q0,pc)
	      val qa0 = down(attrsIdx,q1)
	      val qa1 = deltaA(qa0,atts)
	      val pa = up(attrsIdx,qa1)
	      val q2 = side(q1,pa)
	    in 
	      (upRegExpNames(a,q2,regExpRules),pa,q1,pc,lsc)
	    end
	       
	  (*--------------------------------------------------------------*)
	  (* q = current state                                            *)
	  (* f = current forest                                           *)
	  (* t = current tree                                             *)
	  (* l = label for a subtree                                      *)
	  (*--------------------------------------------------------------*)
	  fun doForest getTree doTree (q,f)=
	    let 
	      fun doit (ls,q,i) = 
		if i<0 then (Vector.fromList ls,q)
		else 
		  let 
		    val t = getTree (f,i)
		    val (p,pa,q',pc,lsc) = doTree(q,t)
		    val q1 = side(q,p)
		  in 
		    doit (LABEL(q1,p,pa,q',pc,lsc)::ls,q1,i-1)
		  end
	    in 
	      doit(nil,q,Vector.length f-1)
	    end

	  fun doAttrs (q,atts) =
	    let 
	      val len = Vector.length atts
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
	    in 
	      doit(q,0)
	    end

	  fun getTree (f,i) =
	    let
	      val (pos,t) = Vector.sub (f,i)
	    in
	      t
	    end

	  fun deltaT (q,t) =
	    case t of 
	      T_TEXT txt => doText q txt
	    | T_PI (target,cont) => doPi q (target,cont) (doForest getTree deltaT) doAttrs
	    | T_ELEM (a,atts,cont) => doElem q (a,atts,cont) (doForest getTree deltaT) doAttrs

	  val deltaF = doForest getTree deltaT

	  (*---------------------------------------------------*)
	  (* possibly do some debugging output                 *)
	  (*---------------------------------------------------*)
	  fun debugArg() = 
	    if !O_GREP_DEBUG<=1 then ()
	    else let val pArr = IntListDict.extractDict pDict
		     val (pAll,pMax,xsMax) = Array.foldl 
		       (fn ((ks,(xs,_)),(all,maxKs,maxXs)) => 
			(all+length ks,Int.max(length ks,maxKs),Int.max(length xs,maxXs)))
		       (0,0,0) pArr
		     val qArr = IntListDict.extractDict qDict
		     val (qAll,qMax,elsMax,txtMax,dfaMax) = Array.foldl 
		       (fn ((ys,(els,txts,_,_)),(all,maxYs,maxEls,maxTxts,maxDfas)) 
			=> let val (nTxts,nDfas) = case txts
			of NONE => (0,0)
		      | SOME(txts,dfas) => 
			  (length txts,length dfas)
			   in (all+length ys,Int.max(length ys,maxYs),
			       Int.max(length(getOpt(els,nil)),maxEls),
			       Int.max(nTxts,maxTxts),Int.max(nDfas,maxDfas)) 
			   end)
		       (0,0,0,0,0) qArr 
		     val Int2String = (StringCvt.padLeft #" " 6) o Int.toString
		     val Real2String = (StringCvt.padLeft #" " 6) 
		       o (Real.fmt (StringCvt.FIX(SOME 1)))
		 in app print
		   ["After R->L pass:\n  ",
		    Int2String (Array.length pArr)," tree states\n  ",
		    Int2String (Array.length qArr)," forest states\n  ",
		    Int2String (IntPairDict.usedIndices downDict),
		    " down transitions\n  ",
		    Int2String (IntPairDict.usedIndices upDict),
		    " up transitions\n  ",
		    Int2String (IntIntListDict.usedIndices tupDict),
		    " text-up transitions\n  ",
		    Int2String (IntPairDict.usedIndices sideDict),
		    " side transitions\n  ",
		    Int2String pMax," maximal size of a tree state\n  ",
		    Real2String(Real.fromInt pAll/Real.fromInt(Array.length pArr)),
		    " average size of a tree state\n  ",
		    Int2String qMax," maximal size of a forest state\n  ",
		    Real2String(Real.fromInt qAll/Real.fromInt(Array.length qArr)),
		    " average size of a forest state\n  ",
		    Int2String xsMax," maximum number of xs for a tree state\n  ",
		    Int2String elsMax,
		    " maximum number of element rules for a forest state\n  ",
		    Int2String txtMax,
		    " maximum number of text rules for a forest state\n  ",
		    Int2String dfaMax,
		    " maximum number of text dfas for a forest state\n\n"
		    ]
		 end

	in 
	  val runArg = deltaF
	  val (doText,doPi,doElem,doForest,doAttrs) = (doText,doPi,doElem,doForest,doAttrs)
	  val debugArg = debugArg
	end

	fun trans_for_y y = let val (_,_,_,_,trans,_,_) = Vector.sub(yVec,y) in trans end
	fun yFs_for_y y = let val (_,_,_,_,_,yFs,_) = Vector.sub(yVec,y) in yFs end
	fun pat_of_y y = let val (_,_,_,_,_,_,num) = Vector.sub(yVec,y) in num end
	fun yFs_for_rule rule = #3(Fs_for_rule rule)

	(*--------------------------------------------------------------*)
	(* yFs_for_q q = { y_F | y in q, (_,x,y)in delta, y_F in F_j    *)
	(*                       _ -> _<... && + re_j && ...>         } *)
	(*--------------------------------------------------------------*)
	fun yFs_for_q q =
	  case getQinfo q 
	    of (_,_,SOME c,_) => c
	  | (a,b,NONE,d) => let val ys = getQstate q
			      val c = foldl 
				(fn (y,yFs) => cupIntLists(yFs_for_y y,yFs)) nil ys
			  in c before setQinfo(q,(a,b,SOME c,d))
			  end

	(*--------------------------------------------------------------*)
	(* yFs_for_q q = { y_F | y in q, (_,x,y)in delta, y_F in F_j    *)
	(*                       _ -> _<... && + re_j && ...>         } *)
	(*--------------------------------------------------------------*)
	fun yFs_for_p p =
	  case getPinfo p 
	    of (_,SOME b) => b
	  | (a,NONE) => let val ks = getPstate p
			    val b = foldl 
			      (fn (k,yFs) => cupIntLists(yFs_for_rule k,yFs)) nil ks
			in b before setPinfo(p,(a,SOME b))
			end

	(*--------------------------------------------------------------*)
	(* down a qr p q = {y | y_F_j, y in q cap qr,                   *)
	(*                      (y,x,y_1) in delta, k in p,             *)
	(*                      x -> a<...&& + re_j &&...> }            *)
	(*--------------------------------------------------------------*)
	val downDict = IntTripleDict.makeDict ("down transition",!O_TS_MATCH,0)
	fun down(a,qq,p) = 
	  case IntTripleDict.hasIndex(downDict,(a,qq,p))
	    of SOME i => IntTripleDict.getByIndex(downDict,i)
	  | NONE => let 
		      val qqr_yFs = (yFs_for_q qq)
                      val yFs = capIntLists(yFs_for_p p,qqr_yFs)
		      val qF = getQindex yFs
		    in
		      qF before IntTripleDict.setByKey(downDict,(a,qq,p),qF)
		    end

	(*--------------------------------------------------------------*)
	(* side q p = { y1 | y in q, k in p, (y1,x^k,y)in delta }       *)
	(*--------------------------------------------------------------*)
	val sideDict = IntPairDict.makeDict ("side transition",!O_TS_MATCH,0)
	fun side(q,p) =
	  case IntPairDict.hasIndex(sideDict,(q,p))
	    of SOME i => IntPairDict.getByIndex(sideDict,i)
	  | NONE => 
	      let 
		val ys = getQstate q
		val xs = xs_of_p p
		val y1ss = map 
		  (fn y => 
		   let 
		     val trans = trans_for_y y
		     val ys = List.concat (selectIntList (xs,trans))
		   in
		     ys
		   end)
		  ys
		val y1s = sortInt (List.concat y1ss)
		val q1 = getQindex y1s
	      in 
		q1 before IntPairDict.setByKey(sideDict,(q,p),q1)
	      end

	(*don't need a side dict since I must consider every transition  every time*)
	fun sideMatchInfo secUnion (dict,qq) =
	  let
	    val ys = getQstate qq
	    (* only y from the ys will be propagated;some info carried 
	      in the dict might be dropped off since not all ys from 
              the preceding side transition were valid *)
	      val (dict1,y1ss) = List.foldl
		(fn (y,(dict2,y1ss)) => 
		 let 
		   val matchInfo = IntListMap.find (dict,y)
		   val [(incomingX,ys)] = trans_for_y y
		   val dict3 =
		     List.foldl 
		     (fn (y,dict4) =>
		      case IntListMap.find (dict4,y) of
			NONE => 
			  (case matchInfo of
			     SOME matchInfo =>
			       IntListMap.insert
			       (dict4,y,matchInfo)
			   | _ => dict4)
		      | SOME (matchInfo2 as (is2,targets2')) => 
			     (case matchInfo of
				SOME (is,targets2) =>
				  IntListMap.insert
				  (dict4,y,
				   (IntSet.union (is2,is),secUnion(targets2',targets2)))
			      | _ =>
				  IntListMap.insert (dict4,y,matchInfo2)
				  ) 
				) dict2 ys
		 in
		   (dict3,ys::y1ss)
		 end) (IntListMap.empty,[]) ys
	      val y1s = sortInt (List.concat y1ss)
	      val q1 = getQindex y1s
	    in 
	      (dict1,q1)
	    end

	(*---------------------------------------------------*)
	(* possibly do some debugging output                 *)
	(*---------------------------------------------------*)
	fun debugBlg() = 
	  if !O_GREP_DEBUG<=1 then ()
	  else let val qArr = IntListDict.extractDict qDict
		   val (qAll,qMax,elsMax) = Array.foldl 
		     (fn ((ys,(_,_,els,_)),(all,maxYs,maxEls)) 
		      =>  (all+length ys,Int.max(length ys,maxYs),
			   Int.max(length(getOpt(els,nil)),maxEls)))
		     (0,0,0) qArr 
		   val Int2String = (StringCvt.padLeft #" " 6) o Int.toString
		   val Real2String = (StringCvt.padLeft #" " 6) 
		     o (Real.fmt (StringCvt.FIX(SOME 1)))
	       in app print
		 ["After L->R pass:\n  ",
		  Int2String (Array.length qArr)," forest states\n  ",
		  Int2String (IntTripleDict.usedIndices downDict),
		  " down transitions\n  ",
		  Int2String (IntPairDict.usedIndices sideDict),
		  " side transitions\n  ",
		  Int2String qMax," maximal size of a forest state\n  ",
		  Real2String(Real.fromInt qAll/Real.fromInt(Array.length qArr)),
		  " average size of a forest state\n  ",
		  Int2String elsMax,
		  " maximum number of element rules for a forest state\n\n"
		  ]
	       end

      in
	(pat_of_y,getIntersection,getPstate,Fs_for_rule,xs_of_p,yFs_for_p,
	 trans_for_y,yFs_for_q,getQindex,getQstate,getQinfo,setQinfo,runArg,
	 (doText,doPi,doElem,doForest,doAttrs),debugArg,down,side,sideMatchInfo,debugBlg)
      end
  end