structure Transitions =
  struct

    open IntLists MatchUtil

    val O_TS_MATCH = ref 5
    type Qinfo = 
      bool option * (* mightMatch *)
      (bool * int list * int list vector) vector option * (* matches *)
      IntList option * (* y0_s_for_q *)
      ((int * int option) list * (int * TextDfa.Dfa) list) option * (* txt rules *)
      bool option * (* mightMatchAfterTag *)
      bool option (* mightMatchAfterAtt *)
    type Pinfo = (* for a given set of rules ks *)
      IntList (* the xs on the lhs *)
    type Tables = 
      {aVec       : Pre.AVector,
       yVec       : PreAlg.YVector,
       rhsVec     : Pre.RhsVector,
       tpVec      : Pre.TextPatternsVector,
       otherRules : IntList,
       otherY0s   : IntList,
       ys_of_y    : Pre.YTargetsVector,
       doMatch    : Pre.DoMatch vector,
       regExpNameRules : (int * TextDfa.Dfa * int list) list,
       preForm    : Pre.YsFormula option Pre.Spec,
       preFormAfterTag    : Pre.YsFormula Pre.Spec,
       preFormAfterAtts    : Pre.YsFormula Pre.Spec,
       postForm   : Pre.YsFormula Pre.Spec,
       pDict : Pinfo IntListDict.Dict,
       qDict : Qinfo IntListDict.Dict,
       downDict : int IntPairDict.Dict,
       upDict : int IntPairDict.Dict,
       tupDict : int IntIntListDict.Dict,
       sideDict : int IntPairDict.Dict,
       elDict : (int list * int list) IntDict.Dict
       }

    fun x_of_rule rhsVec rule = let val (x,_,_) = Vector.sub(rhsVec,rule) in x end
    fun y0s_for_y yVec y = let val (_,_,y0s,_,_) = Vector.sub(yVec,y) in y0s end
    fun trans_for_y yVec y = let val (_,trans,_,_,_) = Vector.sub(yVec,y) in trans end
    fun txt_rules_for_y yVec y = let val (_,_,_,rules,_) = Vector.sub(yVec,y) in rules end
    fun pat_of_y yVec y = let val (_,_,_,_,num) = Vector.sub(yVec,y) in num end

    fun rules_for_a (aVec,other) a = 
      let val (rules,_) = Vector.sub(aVec,a) in rules end handle Subscript => other
    fun y0s_for_a (aVec,other) a = 
      let val (_,y0s) = Vector.sub(aVec,a) in y0s end handle Subscript => other
    fun Fs_for_rule rhsVec rule = let val (_,Fs,_) = Vector.sub(rhsVec,rule) in Fs end
    fun tp_for_rule rhsVec rule = let val (_,_,tp) = Vector.sub(rhsVec,rule) in (rule,tp) end
    fun dfa_for_tp tpVec tp = (tp,Vector.sub(tpVec,tp))
      
    fun hasTransition (dict,pair) = 
      case IntPairDict.hasIndex(dict,pair) 
	of NONE => NONE
      | SOME i => SOME (IntPairDict.getByIndex(dict,i))
    fun setTransition (dict,pair,res) = IntPairDict.setByKey(dict,pair,res)
         
    val hasUp = hasTransition 
    val hasDown = hasTransition
    val hasSide = hasTransition
    val setUp = setTransition
    val setDown = setTransition
    val setSide = setTransition



    fun elDictLookup ({elDict,regExpNameRules,...}:Tables) (dtd,a) =
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
	
    fun getPindex (pDict,rhsVec,ks) = 
      case IntListDict.hasIndex(pDict,ks) of 
	SOME i => i
      | NONE => let val xs = MatchUtil.sortInt (map (x_of_rule rhsVec) ks)
		    val i = IntListDict.getIndex(pDict,ks)
		in i before IntListDict.setByIndex(pDict,i,xs) 
		end
    val getPstate = IntListDict.getKey
    val getPinfo  = IntListDict.getByIndex
    val setPinfo  = IntListDict.setByIndex
    val xs_of_p   = getPinfo
  
    val getQstate = IntListDict.getKey
    val getQindex = IntListDict.getIndex
    val getQinfo  = IntListDict.getByIndex
    val setQinfo = IntListDict.setByIndex

    fun getMatchInfo (ys,(primaries,secondaries),(f1,f2s)) = 
      let
	val m = Formula.eval (fn ys1 => capIntLists(ys,ys1)<>nil) f1
	val prim = 
	  if m then capIntLists (ys,primaries) 
	  else nil (* no info has to be propagated *)
(*! rather than a vector, the sec could also be a list with explicit 
 secondary order paired with ys; could check a trade-off space/speed *)
	val sec = 
	  Vector.mapi 
	  (fn (i,s) => 
	   let
	     val formula = Vector.sub(f2s,i)
	     val m = Formula.eval (fn ys1 => capIntLists(ys,ys1)<>nil) formula
(* as secondaries alone are never reported, the info as to what states 
have to carry sec match info is enough; don't have to return m also, 
as opposed to m for primaries *)
	   in
	     if m then capIntLists(ys,s) else nil
	   end) 
	  (secondaries,0,NONE)
      in
	(m,prim,sec)
      end

    fun matches ({qDict,doMatch,postForm,...} : Tables) q =
      case getQinfo (qDict,q) of 
	(_,SOME b,_,_,_,_) => b
      | (a,NONE,c,d,e,f) => 
	  let 
	    val ys = getQstate (qDict,q)
	    val b = 
	      Vector.mapi 
	      (fn (i,carry) => getMatchInfo (ys,carry,Vector.sub(postForm,i))) 
	      (doMatch,0,NONE)
	  in 
	    b before setQinfo (qDict,q,(a,SOME b,c,d,e,f))
	  end

	(* might functions are used only in the case of one pass without binaries *)
    fun mightMatch ({preForm,qDict,...} : Tables) q =
      case getQinfo (qDict,q) of 
	(SOME a,_,_,_,_,_) => a
      | (NONE,b,c,d,e,f) => 
	  let 
	    val ys = getQstate (qDict,q)
	    val a = 
	      case (#1 (Vector.sub(preForm,0))) of
		NONE => true
	      | SOME f => Formula.eval (fn ys1 => capIntLists(ys,ys1)<>nil) f
	  in 
	    a before setQinfo (qDict,q,(SOME a,b,c,d,e,f))
	  end

    fun mightMatchAfterTag ({preFormAfterTag,qDict,...} : Tables) q =
      case getQinfo (qDict,q) of 
	(_,_,_,_,SOME e,_) => e
      | (a,b,c,d,NONE,f) => 
	  let 
	    val ys = getQstate (qDict,q)
	    val e = Formula.eval (fn ys1 => capIntLists(ys,ys1)<>nil) 
	      (#1 (Vector.sub(preFormAfterTag,0)))
	  in 
	    e before setQinfo(qDict,q,(a,b,c,d,SOME e,f))
	  end

    fun mightMatchAfterAtts ({preFormAfterAtts,qDict,...} : Tables) q =
      case getQinfo (qDict,q) of 
	(_,_,_,_,_,SOME f) => f
      | (a,b,c,d,e,NONE) => 
	  let 
	    val ys = getQstate (qDict,q)
	    val f = Formula.eval (fn ys1 => capIntLists(ys,ys1)<>nil) 
	      (#1 (Vector.sub(preFormAfterAtts,0)))
	  in 
	    f before setQinfo(qDict,q,(a,b,c,d,e,SOME f))
	  end

    (*--------------------------------------------------------------*)
    (* y0s_for_q q = { y_(0,j) | y in q, (y,x,_)in delta,           *)
    (*                           x -> _<... && _ re_j && ...> }     *)
    (*--------------------------------------------------------------*)
    fun y0s_for_q yVec (qDict,q) =
      case getQinfo (qDict,q) of 
	(_,_,SOME c,_,_,_) => c
      | (a,b,NONE,d,e,f) => 
	  let 
	    val ys = getQstate (qDict,q)
	    val c = foldl 
	      (fn (y,y0s) => cupIntLists(y0s_for_y yVec y,y0s)) nil ys
	  in 
	    c before setQinfo(qDict,q,(a,b,SOME c,d,e,f))
	  end

    (*--------------------------------------------------------------*)
    (* txt_rules_for_q q = { k | y in q, (y,x,y_1)in delta,         *)
    (*                           rules[k] = x -> "_" }              *)
    (* return { (k,tp) | rules[k] = _ -> "tp" }                     *)
    (*    and { (tp,dfa) | rules[k] = _ -> "tp", k in txt_rules }   *)
    (*--------------------------------------------------------------*)
    fun txt_rules_for_q (yVec,rhsVec,tpVec) (qDict,q) =
      case getQinfo (qDict,q) of 
	(_,_,_,SOME d,_,_) => d
      | (a,b,c,NONE,e,f) => 
	  let 
	    val ys = getQstate (qDict,q)
	    val rules = foldl 
	      (fn (y,ks) => cupIntLists(txt_rules_for_y yVec y,ks)) nil ys
	    val ktps = map (tp_for_rule rhsVec) rules
	    val tps = MatchUtil.sortInt (List.mapPartial #2 ktps)
	    val dfas = map (dfa_for_tp tpVec) tps
	    val d = (ktps,dfas)
	  in 
	    d before setQinfo(qDict,q,(a,b,c,SOME d,e,f))
	  end

    (*--------------------------------------------------------------*)
    (* down a q = {y_{0,j} | y in q, (y,x,y_1) in delta,            *)
    (*                       x -> a<...&& _ re_j &&...> }           *)
    (*--------------------------------------------------------------*)
    fun down ({aVec,rhsVec,otherY0s,yVec,qDict,downDict,...} : Tables) (a,q) = 
      case hasDown(downDict,(a,q))
	of SOME q0 => q0
      | NONE => let val y0s = capIntLists (y0s_for_q yVec (qDict,q),y0s_for_a (aVec,otherY0s) a)
		    val q0 = getQindex (qDict,y0s)
		in
		  q0 before setDown(downDict,(a,q),q0)
		end
    fun downRegExpNames ({aVec,rhsVec,otherY0s,yVec,qDict,downDict,...}:Tables) (a,q,y0s_regExpRules) = 
      case hasDown(downDict,(a,q)) of 
	SOME q0 => q0
      | NONE => 
	  let 
	    val y0s = capIntLists
	      (cupIntLists (y0s_for_a (aVec,otherY0s) a,y0s_regExpRules),
	       y0s_for_q yVec (qDict,q))
	    val q0 = getQindex (qDict,y0s)
	  in 
	    q0 before setDown(downDict,(a,q),q0)
	  end

    (*--------------------------------------------------------------*)
    (* up a q = {k | rules[k]= _ -> a<e_k>,                         *)
    (*               q cap F_j <> 0 for e_k = ...&& +re_j &&...,    *)
    (*               q cap F_j =  0 for e_k = ...&& -re_j &&... }   *)
    (*--------------------------------------------------------------*)
    fun up ({aVec,rhsVec,otherRules,qDict,upDict,pDict,...} : Tables) (a,q) = 
      case hasUp(upDict,(a,q)) 
	of SOME p => p
      | NONE => let val ys = getQstate (qDict,q)
		    val ks = List.filter 
		      (fn rule => 
		       let val (posFs,negFs,_,_) = Fs_for_rule rhsVec rule
		       in if capIntLists(ys,negFs)<>nil then false
			  else List.all (fn posF => capIntLists(ys,posF)<>nil) posFs
		       end) (rules_for_a (aVec,otherRules) a)
		    val p = getPindex(pDict,rhsVec,ks)
		in 
		  p before setUp (upDict,(a,q),p)
		end
    fun upRegExpNames ({aVec,rhsVec,otherRules,qDict,upDict,pDict,...} : Tables) (a,q,regExpRules) = 
      case hasUp(upDict,(a,q)) 
	of SOME p => p
      | NONE => 
	  let 
	    val ys = getQstate (qDict,q)
	    fun filterRule rule = 
	      let 
		val (posFs,negFs,_,_) = Fs_for_rule rhsVec rule
	      in 
		if capIntLists(ys,negFs)<>nil then false
		else List.all (fn posF => capIntLists(ys,posF)<>nil) posFs
	      end
	    val ks = List.filter filterRule (rules_for_a (aVec,otherRules) a)
	    val ks_regExp = List.filter filterRule regExpRules
	    val ks = cupIntLists (ks,rev ks_regExp)
	    val p = getPindex (pDict,rhsVec,ks)
	  in 
	    p before setUp (upDict,(a,q),p)
	  end

    (*--------------------------------------------------------------*)
    (* assure that txt_rules_for q = (ktps,_). Then                 *)
    (* txt_up q matches = { k | (k,tp) in ktps, tp in matches }.    *)
    (*--------------------------------------------------------------*)
    fun txt_up rhsVec (pDict,tupDict,q,ktps,matches) = 
      case IntIntListDict.hasIndex(tupDict,(q,matches)) of 
	SOME i => IntIntListDict.getByIndex(tupDict,i)
      | NONE => let
		  val ks = List.mapPartial 
		    (fn (k,tp) => 
		     case tp 
		       of NONE => SOME k
		     | SOME i => if inIntList(i,matches) then SOME k else NONE) 
		    ktps 
		  val p = getPindex(pDict,rhsVec,ks)
		in 
		  p before IntIntListDict.setByKey(tupDict,(q,matches),p)
		end
                   
    (*--------------------------------------------------------------*)
    (* side q p = { y1 | y in q, k in p, (y,x^k,y1)in delta }       *)
    (*--------------------------------------------------------------*)
    fun side ({yVec,sideDict,qDict,pDict,...} : Tables) (q,p) =
      case hasSide(sideDict,(q,p))
	of SOME q1 => q1
      | NONE => let val ys = getQstate (qDict,q)
		    val xs = xs_of_p (pDict,p)
		    val y1ss = map 
		      (fn y => let val trans = trans_for_y yVec y
			       in List.concat (selectIntList (xs,trans))
			       end)
		      ys
		    val y1s = sortInt (List.concat y1ss)
		    val q1 = getQindex (qDict,y1s)
		in q1 before setSide(sideDict,(q,p),q1)
		end


    fun sideMatchInfo ({yVec,pDict,qDict,sideDict,...} : Tables) 
      matchMapTransition
      (dict,q,p) =
	let 
	  val ys = getQstate (qDict,q)
	  val xs = xs_of_p (pDict,p)
	  val dict = 
	    matchMapTransition
	    (fn y => List.concat (selectIntList (xs,trans_for_y yVec y))) 
	    dict 
	  val yss = 
	    List.foldl 
	    (fn (y,yss) => 
	     let
	       val trans = trans_for_y yVec y
	       val ys =
		 List.concat (selectIntList (xs,trans))
	     in
	       ys::yss
	     end) [] ys
	  val y1s = sortInt (List.concat yss)
	  val q1 = getQindex(qDict,y1s)
	in 
	  (dict,q1) before setSide(sideDict,(q,p),q1)
	end

		    
    (*--------------------------------------------------------------*)
    (* text q txt = { k | y in q, (y,x,y_1) in delta,               *)
    (*                    rules[k] = x -> "tp", txt match tp. }     *)
    (*--------------------------------------------------------------*)
    fun text ({yVec,rhsVec,tpVec,pDict,tupDict,qDict,...} : Tables) (q,txt) = 
      let 
	val (ktps,dfas) = txt_rules_for_q (yVec,rhsVec,tpVec) (qDict,q)
	val matches = TextDfa.runDfas dfas txt
      in txt_up rhsVec (pDict,tupDict,q,ktps,matches)
      end

      (*--------------------------------------------------------------*)
      (* Process the attributes of an element                         *)
      (*--------------------------------------------------------------*)
      fun deltaA tabs (q,atts) =
         let val len = Vector.length atts
            fun doit (q,i) = 
               if i>=len then q
               else let val (a,txt) = Vector.sub(atts,i) 
                        val qa0 = down tabs (a,q)
                        val pa = text tabs (qa0,txt)
                        val qa1 = side tabs (qa0,pa)
                        val p = up tabs (a,qa1)
                        val q1 = side tabs (q,p)
                    in doit(q1,i+1)
                    end
         in doit(q,0)
         end

    fun matchMapTransition secUnion trans matchMap =
      let
	fun side matchMap trans (y,matchInfo as (is,targets2)) secUnion =
	  List.foldl
	  (fn (y,matchMap1) =>
	   case (IntListMap.find (matchMap1,y)) of
	     NONE => 
	       IntListMap.insert (matchMap1,y,matchInfo)
	   | SOME (is',targets2') => 
	       IntListMap.insert 
	       (matchMap1,y,
		(IntSet.union (is,is'),secUnion (targets2,targets2')))
	       ) matchMap (trans y)
      in
	IntListMap.foldli 
	(fn (y,matchInfo,matchMap) => side matchMap trans (y,matchInfo) secUnion)
	IntListMap.empty matchMap
      end

    fun transOnePass ({qDict,ys_of_y,...} : Tables) q1 y =
      IntLists.capIntLists (Vector.sub (ys_of_y,y),getQstate (qDict,q1))

    fun initTables ((yVec,aVec,rhsVec,tpVec,otherRules,
		     otherY0s,q0,doMatch,ys_of_y,
		     regExpNameRules,preForm,preFormAfterTag,
		     preFormAfterAtts,postForm):PreAlg.PreAlg) =
      let
	val qDict = IntListDict.makeDict ("forest state",!O_TS_MATCH,(NONE,NONE,NONE,NONE,NONE,NONE):Qinfo)
	val q0 = IntListDict.getIndex(qDict,q0)
	val tab =
	  {aVec       = aVec,  
	    yVec       = yVec,  
	    rhsVec     = rhsVec,  
	    tpVec      = tpVec,
	    otherRules = otherRules,
	    otherY0s   = otherY0s,
	    doMatch    = doMatch,
	    ys_of_y    = ys_of_y,
	    regExpNameRules = regExpNameRules,
	    preForm = preForm, 
	    preFormAfterTag = preFormAfterTag,
	    preFormAfterAtts = preFormAfterAtts,
	    postForm = postForm,
	    pDict = IntListDict.makeDict ("tree state",!O_TS_MATCH,nil:Pinfo),
	    qDict = qDict,
	    downDict = IntPairDict.makeDict ("down transition",!O_TS_MATCH,0),
	    upDict   = IntPairDict.makeDict ("up transition",!O_TS_MATCH,0),
	    tupDict  = IntIntListDict.makeDict ("text up transition",!O_TS_MATCH,0),
	    sideDict = IntPairDict.makeDict ("side transition",!O_TS_MATCH,0),
	    elDict   = IntDict.makeDict ("element names and nfa-s",!O_TS_MATCH,(nil,nil))
	    } : Tables
      in
	(tab,q0)
      end

    fun debug ({qDict,pDict,sideDict,tupDict,upDict,downDict,...} : Tables) () =
	  if !GrepOptions.O_GREP_DEBUG<=1 then ()
	  else let val pArr = IntListDict.extractDict pDict
		   val (pAll,pMax,xsMax) = Array.foldl 
		     (fn ((ks,xs),(all,maxKs,maxXs)) => 
		      (all+length ks,Int.max(length ks,maxKs),Int.max(length xs,maxXs)))
		     (0,0,0) pArr
		   val qArr = IntListDict.extractDict qDict
		   val (qAll,qMax,elsMax,txtMax,dfaMax) = Array.foldl 
		     (fn ((ys,(_,_,els,txts,_,_)),(all,maxYs,maxEls,maxTxts,maxDfas)) 
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
		 ["Matched after parsing:\n  ",
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


    fun getTransitions preAlg =
      let
	val (tab,q0) = initTables preAlg
      in
	(q0,down tab,downRegExpNames tab,up tab,
	 upRegExpNames tab,side tab,sideMatchInfo tab,text tab,
	 mightMatch tab,mightMatchAfterTag tab,mightMatchAfterAtts tab,
	 matches tab,elDictLookup tab,deltaA tab,transOnePass tab,debug tab)
      end

  end
