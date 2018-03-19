signature Match2Hooks =
   sig
      type AppData
      val matchStart : DocDtd.Dtd * PreAlg.PreAlg -> AppData
   end

structure Match2Hooks0 =
   struct
     val THIS_MODULE = "Match2Hooks"

     open
       Encoding Errors HookData IgnoreHooks UniChar
       DocDtd GrepError IntLists MatchData MatchOptions MatchReport MatchUtil 
       Transitions

      val suggestedSize = 100
      val matchTable = 
	DynamicArray.array 
	(suggestedSize,
	 ((("uninitialized",0,0),MatchData.T_TEXT #[]),
	  IntListMap.empty:NodeSet.set IntListMap.map))
          		    
      exception DocFail = DocHooks.DocFail

      type ForestState = int
      type Cont = (Position * Tree) list
      type Curr = (int * ((IntSet.set * NodeSet.set IntListMap.map) IntListMap.map)) * 
	Cont * ForestState * int list
      type Parent = Cont * Position * int * AttSpc vector * ForestState * ForestState * 
	((IntSet.set * NodeSet.set IntListMap.map) IntListMap.map) * int list

      type AppData = Encoding.Encoding * Dtd * Tables * (Position * Vector) list * Curr * Parent list 
      type AppFinal = unit

      fun matchStart (dtd,pre) = 
	let 
	  val (tabs,q0) = initTables pre
	in 
	  (Encoding.ASCII,dtd,tabs,nil, ((0,IntListMap.empty),nil,q0,nil),nil) : AppData
	end

      fun hookXml ((_,dtd,tabs,vecs,((j,dict),c,q,regExpRules),parents),
		  (_,enc:Encoding.Encoding,opt)) =
	(enc,dtd,tabs,vecs,((j,dict),c,q,regExpRules),parents)

      fun posOf (pos,_) = pos

      fun addData ((enc,dtd,tabs,vecs,curr,parents),pos,vec) =
         (enc,dtd,tabs,(pos,vec)::vecs,curr,parents)
         
      fun hookData (a,((pos,_),vec,_)) = addData(a,pos,vec)
      fun hookCData (a,((pos,_),vec)) = addData(a,pos,vec)
      fun hookCharRef (a,((pos,_),c,_)) = addData(a,pos,Vector.fromList [c])

      val nullPos = ("",0,0)
      val emptyTree = T_TEXT #[]

      fun takeData (dtd,tabs,curr,vecs) = 
	if null vecs then curr
	else 
	  let 
	    val vecs = rev vecs
	    val txt = Vector.concat (map #2 vecs)
	  in 
	    if Vector.length txt=0 then curr
	    else 
	      let 
		val ((j,dict),c,q,regExpRules) = curr 
		val p = text tabs (q,txt)
		val (dict,q1) = 
		  sideMatchInfo tabs 
		  (matchMapTransition Match2.secUnion)
		  (dict,q,p)
		val (match,yTargets,secMatches) = Vector.sub(matches tabs q1,0)
		val t = T_TEXT txt
		val pos = posOf (hd vecs)
		val (j,dict) = 
		  Match2.addMatches 
		  (match,yTargets,secMatches,matchTable,j,dict,pos,t)
		val c1 = (pos,t)::c
		val curr1 = ((j,dict),c1,q1,regExpRules)
	      in 
		curr1
	      end
	  end

	
      fun hookProcInst ((enc,dtd,tabs,vecs,curr,parents),
			((pos,_),target,tpos,text)) =
         let 
(* dict from siblings and other dict as for end tag are not needed 
as there can be no match below a pi node *)
            val target = Data2Vector target
            val ((j,dict1),c,q,regExpRules) = takeData (dtd,tabs,curr,vecs)
            val q0 = down tabs (piIdx,q)
            val qa0 = down tabs (attrsIdx,q0)
            val qa1 = deltaA tabs (qa0,Vector.fromList[(targetIdxE,target)])
            val pa = up tabs (attrsIdx,qa1)
            val q1 = side tabs (q0,pa)
            val qc0 = down tabs (contentIdx,q1)
            val ((j,dict1),ct,qc1,regExpRules) = 
	      takeData (dtd,tabs,((j,dict1),nil,qc0,regExpRules),[(tpos,text)])
            val pc = up tabs (contentIdx,qc1)
            val q2 = side tabs (q1,pc)
            val p = up tabs (piIdx,q2)
            val q1 = side tabs (q,p)
	    val (match,yTargets,secMatches) = Vector.sub(matches tabs q1,0)
            val t = T_PI(target,Vector.fromList [(tpos,T_TEXT text)]) 
	    val (j,dict1) = Match2.addMatches
	      (match,yTargets,secMatches,matchTable,j,dict1,pos,t)
            val c1 = (pos,t)::c
            val curr2 = ((j,dict1),c1,q1,regExpRules)
         in 
	   (enc,dtd,tabs,nil,curr2,parents):AppData
         end

      fun hookEndTag ((enc,dtd,tabs,vecs,curr,parents),_) =
         case parents 
           of nil => raise InternalError (THIS_MODULE,"hookEndTag","empty stack")
            | (c,pos,a,atts,q,q1,dict,regExpRulesParent)::parents =>
              let 
                 val ((j,dict1),ct,qc1,regExpRules) = takeData (dtd,tabs,curr,vecs)     
                 val pc = up tabs (contentIdx,qc1)
                 val q2 = side tabs (q1,pc)
		 val dict1 = 
		   matchMapTransition Match2.secUnion (transOnePass tabs q2) dict1
                 val p = upRegExpNames tabs (a,q2,regExpRules)
                 val (dict,q1) = sideMatchInfo tabs 
		   (matchMapTransition Match2.secUnion) 
		   (dict,q,p)
		 val dict1 = 
		   matchMapTransition Match2.secUnion (transOnePass tabs q1) dict1
		 val dict =
		   Match2.matchMapUnion matchTable (dict,dict1) 
		   (IntListMap.unionWith NodeSet.union) DynamicArray.sub DynamicArray.update
                 val (match,yTargets,secMatches) = Vector.sub(matches tabs q1,0)
                 val t = 
		   T_ELEM(a,atts,Vector.fromList (rev ct))
		 val (j,dict) = Match2.addMatches 
		   (match,yTargets,secMatches,matchTable,j,dict,pos,t)
		 val c1 = (pos,t)::c
                 val curr1 = ((j,dict),c1,q1,regExpRulesParent)
              in 
		(enc,dtd,tabs,nil,curr1,parents)
              end
                    
      fun hookStartTag ((enc,dtd,tabs, vecs,curr,parents),((pos,_),a,atts,_,mt)) =
	let 
	  val attspecs = List.mapPartial 
	    (fn (i,ap,_) => case ap
	     of AP_DEFAULT(_,av,_) => SOME(DocAtt2Elem dtd i,av)
	   | AP_PRESENT(_,av,_) => SOME(DocAtt2Elem dtd i,av)
	   | _ => NONE) atts
	  val atts = Vector.fromList attspecs
	    
	  val ((j,dict1),c,q,regExpRulesParent) = takeData (dtd,tabs,curr,vecs)       

	  val (y0s_regExpRules,regExpRules) = elDictLookup tabs (dtd,a)

	  val q0 = downRegExpNames tabs (a,q,y0s_regExpRules)
	  val qa0 = down tabs (attrsIdx,q0)
	  val qa1 = deltaA tabs (qa0,atts)
	  val pa = up tabs (attrsIdx,qa1)
	  val q1 = side tabs (q0,pa)
	    
	  val qc0 = down tabs (contentIdx,q1)
	    
	  val parents1 = (c,pos,a,atts,q,q1,dict1,regExpRulesParent)::parents
	  val curr1 = ((j,IntListMap.empty),nil,qc0,regExpRules)
	  val a1 = (enc,dtd,tabs,nil,curr1,parents1)
	in 
	  if mt then hookEndTag(a1,()) else a1
	end

      fun hookWarning (a,warn) = a before printWarning "" warn
      fun hookError (a,err) = 
         let 
            val _ = printError "" err
            val _ = case err 
                      of (_,ERR_NO_SUCH_FILE _) => raise DocFail
                       | _ => ()
         in a
         end

      fun hookFinish (enc,dtd,tabs,_,((j,_),_,_,_),parents) = 
         let 
	   val (enc,(matchTable,j)) = 
	     case parents of 
	       nil => (Encoding.encodingName enc, (matchTable,j))
	     | _ => raise InternalError 
		 (THIS_MODULE,"hookFinish","non-empty stack")
	   val _ = Match2.printMatchTable dtd (matchTable,j,enc)
 	   val _=
	     (*---------------------------------------------------*)
	     (* possibly do some debugging output                 *)
	     (*---------------------------------------------------*)
	     if !O_GREP_DEBUG<=1 then ()
	     else 
	       let 
		 val {pDict,qDict,upDict,downDict,tupDict,sideDict,...} = tabs : Tables
		 val pArr = IntListDict.extractDict pDict
		 val (pAll,pMax,xsMax) = Array.foldl 
		   (fn ((ks,xs),(all,maxKs,maxXs)) => 
		    (all+length ks,Int.max(length ks,maxKs),Int.max(length xs,maxXs)))
		   (0,0,0) pArr
		 val qArr = IntListDict.extractDict qDict
		 val (qAll,qMax,elsMax,txtMax,dfaMax) = 
		   Array.foldl 
		   (fn ((ys,(_,_,els,txts,_,_)),(all,maxYs,maxEls,maxTxts,maxDfas)) 
		    => let 
			 val (nTxts,nDfas) = 
			   case txts
			     of NONE => (0,0)
			   | SOME(txts,dfas) => 
			       (length txts,length dfas)
		       in 
			 (all+length ys,Int.max(length ys,maxYs),
			  Int.max(length(getOpt(els,nil)),maxEls),
			  Int.max(nTxts,maxTxts),Int.max(nDfas,maxDfas)) 
		       end)
		   (0,0,0,0,0) qArr 
		 val Int2String = (StringCvt.padLeft #" " 6) o Int.toString
		 val Real2String = (StringCvt.padLeft #" " 6) 
		   o (Real.fmt (StringCvt.FIX(SOME 1)))
	       in
		 app print
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
	 in
	   ()
	 end
   end

structure Match2Hooks = Match2Hooks0 : Match2Hooks
