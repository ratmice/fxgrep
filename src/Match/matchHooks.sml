signature MatchHooks =
   sig
      type AppData
      val matchStart : DocDtd.Dtd * PreAlg.PreAlg -> AppData
   end

structure MatchHooks0 =
   struct
      open
         Encoding Errors HookData IgnoreHooks UniChar
         DocDtd GrepError IntLists MatchData MatchOptions MatchReport MatchUtil 
	 Transitions
          
      val THIS_MODULE = "MatchHooks"          
			         
      exception DocFail = DocHooks.DocFail

      type ForestState = int
      type Cont = (Position * Tree) list
      type Curr = Cont * Matches list option * Report * bool * ForestState * int list
      type Parent = Cont * Matches list option * bool 
         * Position * int * AttSpc vector * ForestState * ForestState * int list

      type AppData = Dtd * Tables * (Position * Vector) list * Curr * Parent list
      type AppFinal = unit

      fun matchStart (dtd,pre) = 
         let 
	   val (tabs,q0) = initTables pre
         in 
	   (dtd,tabs,nil,(nil,NONE,nullReport,false,q0,nil),nil) : AppData
         end

      fun hookXml((dtd,tabs,vecs,(c,m,_,s,q,regExpRules),parents),(_,enc,opt)) =
	let 
	  val encName = case opt of 
	    SOME(_,SOME encName,_) => encName
	  | _ => encodingName enc
	  val r0 = reportStart encName
	in 
	  (dtd,tabs,vecs,(c,m,r0,s,q,regExpRules),parents)
	end

      fun posOf (pos,_) = pos
      fun reports dtd ms = ReportMatchUtil.reportMatches (report dtd) ms

      fun addData ((dtd,tabs,vecs,curr,parents),pos,vec) =
         (dtd,tabs,(pos,vec)::vecs,curr,parents)
         
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
		val (c,m,r,s,q,regExpRules) = curr 
		val p = text tabs (q,txt)
		val q1 = side tabs (q,p)		  
		val (match,_,_) = Vector.sub(matches tabs q1,0)
		val postree = if match orelse isSome m
				then (posOf(hd vecs),T_TEXT txt)
			      else (nullPos,emptyTree)
                          val (c1,m1,r1,s1) = 
                             if match
                                then case !O_MATCH_SELECT 
                                       of INNER => (c,NONE,report dtd (postree,r),true)
                                        | _ => case m
                                                 of NONE => (c,NONE,report dtd (postree,r),false)
                                                  | SOME ms => 
                                                    (postree::c,SOME(ONE postree::ms),r,false)
                             else case !O_MATCH_SELECT 
                                    of INNER => (c,NONE,r,s) 
                                     | _ => (case m
                                               of NONE => (c,NONE,r,false)
                                                | SOME ms => (postree::c,SOME ms,r,false))
                          val curr1 = (c1,m1,r1,s1,q1,regExpRules)
                      in curr1
                      end
              end

      fun new_cmrs dtd (c,m,s,mt,rt,st,match,pos,t) =
         case !O_MATCH_SELECT 
           of INNER => 
              if st orelse not match then (c,NONE,rt,st orelse s) 
              else (c,NONE,report dtd ((pos,t),rt),true)
            | OUTER => 
              (case m
                 of NONE => 
                    let val r1 = 
                       if match then report dtd ((pos,t),rt)
                       else case mt
                              of NONE => rt
                               | SOME nil => rt
                               | SOME ms => reports dtd (MORE(NONE,ms),rt)
                    in (c,NONE,r1,false)
                    end
                  | SOME ms => 
                    let val ms1 = 
                       if match then ONE(pos,t)::ms
                       else case mt
                              of NONE => ms
                               | SOME nil => ms
                               | SOME ms2 => MORE(NONE,ms2)::ms
                    in ((pos,t)::c,SOME ms1,rt,false)
                    end)
            | ALL => 
              case m of 
		NONE => 
		  let 
		    val r1 = 
                      if match then case mt of 
			NONE => report dtd ((pos,t),rt)
		      | SOME nil => report dtd ((pos,t),rt)
		      | SOME ms => reports dtd
			  (MORE(SOME(pos,t),ms),rt)
                      else case mt of 
			NONE => rt
		      | SOME nil => rt
		      | SOME ms => reports dtd (MORE(NONE,ms),rt)
		  in (c,NONE,r1,false)
		  end
                 | SOME ms => 
                   let val ms1 = 
                      if match then case mt
                                      of NONE => ONE(pos,t)::ms
                                       | SOME nil => ONE(pos,t)::ms
                                       | SOME ms2 => 
                                         MORE(SOME(pos,t),ms2)::ms
                      else case mt
                             of NONE => ms
                              | SOME nil => ms
                              | SOME ms2 => MORE(NONE,ms2)::ms
                   in ((pos,t)::c,SOME ms1,rt,false)
                   end

      fun hookProcInst ((dtd,tabs,vecs,curr,parents):AppData,((pos,_),target,tpos,text)) =
         let 
            val target = Data2Vector target
            val (c,m,r,s,q,regExpRules) = takeData(dtd,tabs,curr,vecs)
            val might = mightMatch tabs q
            val m0 = if isSome m orelse might andalso !O_MATCH_SELECT<>INNER 
		       then SOME nil else m

            val q0 = down tabs (piIdx,q)
            val qa0 = down tabs (attrsIdx,q0)
            val qa1 = deltaA tabs (qa0,Vector.fromList[(targetIdxE,target)])
            val pa = up tabs (attrsIdx,qa1)
            val q1 = side tabs (q0,pa)
            val qc0 = down tabs (contentIdx,q1)
            val (ct,mt,rt,st,qc1,regExpRules) = 
	      takeData (dtd,tabs,(nil,m0,r,false,qc0,regExpRules),[(tpos,text)])
            val pc = up tabs (contentIdx,qc1)
            val q2 = side tabs (q1,pc)
            val p = up tabs (piIdx,q2)
            
            val q1 = side tabs (q,p)
            val (match,_,_) = Vector.sub(matches tabs q1,0)
            val t = if match orelse isSome m 
                       then T_PI(target,Vector.fromList [(tpos,T_TEXT text)]) else emptyTree
            val (c1,m1,r1,s1) = new_cmrs dtd (c,m,s,mt,rt,st,match,pos,t)
            val curr2 = (c1,m1,r1,s1,q1,regExpRules)
         in (dtd,tabs,nil,curr2,parents):AppData
         end

      fun hookEndTag ((dtd,tabs,vecs,curr,parents),_) =
         case parents 
           of nil => raise InternalError (THIS_MODULE,"hookEndTag","empty stack")
            | (c,m,s,pos,a,atts,q,q1,regExpRulesParent)::parents =>
              let 
                 val (ct,mt,rt,st,qc1,regExpRules) = takeData (dtd,tabs,curr,vecs)     
                 val pc = up tabs (contentIdx,qc1)
                 val q2 = side tabs (q1,pc)
                 val p = upRegExpNames tabs (a,q2,regExpRules)
                 val q1 = side tabs (q,p)
                 val (match,_,_) = Vector.sub(matches tabs q1,0)
                 val t =
		   if match orelse isSome m 
		     then T_ELEM(a,atts,Vector.fromList (rev ct)) else emptyTree
                 val (c1,m1,r1,s1) = new_cmrs dtd (c,m,s,mt,rt,st,match,pos,t)
                 val curr1 = (c1,m1,r1,s1,q1,regExpRulesParent)
              in (dtd,tabs,nil,curr1,parents)
              end
                    
      fun hookStartTag ((dtd, tabs, vecs,curr,parents),((pos,_),a,atts,_,mt)) =
         let 
            val attspecs = List.mapPartial 
               (fn (i,ap,_) => case ap
                                 of AP_DEFAULT(_,av,_) => SOME(DocAtt2Elem dtd i,av)
                                  | AP_PRESENT(_,av,_) => SOME(DocAtt2Elem dtd i,av)
                                  | _ => NONE) atts
            val atts = Vector.fromList attspecs
            val (c,m,r,s,q,regExpRulesParent) = takeData (dtd,tabs,curr,vecs)
	    val (y0s_regExpRules,regExpRules) = elDictLookup tabs (dtd,a)

            val q0 = downRegExpNames tabs (a,q,y0s_regExpRules)
            val qa0 = down tabs (attrsIdx,q0)
            val qa1 = deltaA tabs (qa0,atts)
            val pa = up tabs (attrsIdx,qa1)
            val q1 = side tabs (q0,pa)

	    val might = 
	      (mightMatch tabs q) andalso
	      (mightMatchAfterTag tabs q0) andalso
	      (mightMatchAfterAtts tabs q1)

	    val m0 = if isSome m orelse might andalso !O_MATCH_SELECT<>INNER 
		       then SOME nil else m

            val qc0 = down tabs (contentIdx,q1)

            val parents1 = (c,m,s,pos,a,atts,q,q1,regExpRulesParent)::parents
            val curr1 = (nil,m0,r,false,qc0,regExpRules)
            val a1 = (dtd,tabs,nil,curr1,parents1)
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

      fun hookFinish (_,tabs,_,(_,_,r,_,_,_),parents) = 
         let val _ = case parents
                       of nil => reportFinish r
                        | _ => raise InternalError 
                          (THIS_MODULE,"hookFinish","non-empty stack")
         in
            (*---------------------------------------------------*)
            (* possibly do some debugging output                 *)
            (*---------------------------------------------------*)
            if !O_GREP_DEBUG<=1 then ()
            else let val {pDict,qDict,upDict,downDict,tupDict,sideDict,...} = tabs : Tables
                     val pArr = IntListDict.extractDict pDict
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
         end
   end

structure MatchHooks = MatchHooks0 : MatchHooks
