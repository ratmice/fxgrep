signature GramFlatten =
  sig

(* the variables from the grammars plus variables allocated for
attributes and content for different rules for the same variable *)
    type AttsCont = ((int*int) list) IntListMap.map

    type Flat = GramData.FlatGrammar 
      * (GramData.XRegExp * BerryXre.Berry) vector * TextDfa.Dfa vector
      * AttsCont
      
    val flatten  : GramData.Grammar -> Flat
    val flatten' : GramData.Grammar -> 
      Flat * (int * BerryXre.Berry XRegExpDict.Dict * TextDfa.Dfa TextPatternDict.Dict)
  end

structure GramFlatten : GramFlatten =
   struct
      open 
         DocDtd GramData GramTables GramUtil

      type AttsCont = ((int*int) list) IntListMap.map
      type Flat = FlatGrammar * (XRegExp * BerryXre.Berry) vector * TextDfa.Dfa vector * AttsCont


      structure ReDict = XRegExpDict 
      structure TpDict = TextPatternDict 

      val O_RE_DICT_SIZE = ref 4
      val O_TP_DICT_SIZE = ref 4

      val O_SHARE_RE = ref false

      fun flatten' (max,starts,rules) =
         let 
            val reDict = ReDict.makeDict("regular expression",!O_RE_DICT_SIZE,BerryXre.nullBerry)
            val tpDict = TpDict.makeDict("text pattern",!O_TP_DICT_SIZE,TextDfa.nullDfa)

	    val reList = ref []

            fun reIndex re = 
	      if !O_SHARE_RE then
		case ReDict.hasIndex(reDict,re)
		  of SOME i => i
		| NONE => let val i = ReDict.getIndex(reDict,re)
			      val berry = BerryXre.berry re
			      val _ = ReDict.setByIndex(reDict,i,berry)
			  in i
			  end
	      else
		let
		  val l = List.length (!reList)
		  val berry = BerryXre.berry re
		  val _ =  reList:=(re,berry)::(!reList)
		in
		  l
		end


            fun tpIndex tp = 
               if tp=TXT_UNDER then NONE 
               else case TpDict.hasIndex(tpDict,tp)
                      of SOME i => SOME i
                       | NONE => let val i = TpDict.getIndex(tpDict,tp)
                                     val dfa = TextDfa.makeDfa tp
                                     val _ = TpDict.setByIndex(tpDict,i,dfa)
                                 in SOME i
                                 end
                              
            val do_fexp = map (fn (sign,re) => (sign,reIndex re))

            val xDontCare = max
            val XRE_DONTCARE = RE_REP(RE_BASIC xDontCare)
            val feDontCare = [(true,reIndex XRE_DONTCARE)]
            val ruDontCare = [FLAT_ELEM(GI_UNDER,feDontCare),FLAT_TEXT NONE]

            val FE_UNDER = [(true,GramTables.XRE_UNDER)]
   
            fun do_txt (next,rules) tp = 
               (FLAT_TEXT(tpIndex tp),next,rules)
               
            fun do_att (next,rules) (sign,ap) =
               case ap
                 of AT_NAME att => 
                    let 
                       val xAtt = next

                       val reAtt = RE_BASIC xTrue
                       val feAtt = [(true,reIndex reAtt)]
                       val ruAtt = [FLAT_ELEM(GI_POS [att],feAtt)]

                       val reAtts = makeSeq [XRE_DONTCARE,RE_BASIC xAtt,XRE_DONTCARE]
                    in ((sign,reIndex reAtts),next+1,(xAtt,ruAtt)::rules)
                    end
                  | AT_VALUE(att,tp) => 
                    let 
                       val (xAtt,xVal) = (next,next+1)
                       
                       val ruVal = [FLAT_TEXT(tpIndex tp)]

                       val reAtt = RE_BASIC xVal
                       val feAtt = [(true,reIndex reAtt)]
                       val ruAtt = [FLAT_ELEM(GI_POS [att],feAtt)]
                       
                       val reAtts = makeSeq [XRE_DONTCARE,RE_BASIC xAtt,XRE_DONTCARE]
                    in ((sign,reIndex reAtts),next+2,(xVal,ruVal)::(xAtt,ruAtt)::rules)
                    end

            fun do_elem (next,rules) ((gp,atts),fe) =
               let 
                  val (xAtts,next,rules) = 
                     if null atts then (xDontCare,next,rules)
                     else let 
                             val (feAtts,next,rules) = foldl 
                                (fn (att,(fe,next,rules))
                                 => let val (sre,next,rules) = do_att (next,rules) att
                                    in (fe@[sre],next,rules)
                                    end) (nil,next,rules) atts
                             val xAtts = next
                             val ruAtts = [FLAT_ELEM(GI_ATTS,feAtts)]
                          in (xAtts,next+1,(xAtts,ruAtts)::rules)
                          end
                       
                  val (next,rules,xCont) = 
                     if fe=FE_UNDER then (next,rules,xDontCare)
                     else let val xCont = next
                              val feCont = do_fexp fe
                              val ruCont = [FLAT_ELEM(GI_CONT,feCont)]
                          in (next+1,(xCont,ruCont)::rules,xCont)
                          end
                     
                  val reElem = makeSeq [RE_BASIC xAtts,RE_BASIC xCont,XRE_UNDER]
                  val feElem = [(true,reIndex reElem)]
               in 
                  ((xAtts,xCont),(FLAT_ELEM(gp,feElem),next,rules))
               end

            fun do_pi pars (target,fe) =
               do_elem pars ((GI_POS [piIdx],[(true,AT_VALUE(targetIdxE,target))]),fe)

            val (xAttsContVars,(newRules,next,newRules')) = foldl 
	      (fn ((x,rhss),(xAttsContVars,(newRules,next,rules))) => 
	       let 
		 val (attsContVars,(newRhss,next,rules)) = foldl
		   (fn (rhs,(attsContVars,(newRhss,next,rules))) => 
		    case rhs of
		      RHS_TEXT x1 =>
			let 
			   val (newRhs,next,rules)=do_txt (next,rules) x1
			 in
			   (attsContVars,(newRhs::newRhss,next,rules))
			 end
		     | RHS_PI x1 => 
			 let 
			   val ((xAtts,xCont),(newRhs,next,rules))= do_pi (next,rules) x1
			 in
			   ((xAtts,xCont)::attsContVars,(newRhs::newRhss,next,rules))
			 end
		     | RHS_TREE x1 => 
			 let 
			   val ((xAtts,xCont),(newRhs,next,rules))= do_elem (next,rules) x1
			 in
			   ((xAtts,xCont)::attsContVars,(newRhs::newRhss,next,rules))
			 end)
		    (nil,(nil,next,rules)) rhss
	       in 
		 (IntListMap.insert (xAttsContVars,x,attsContVars),
		  ((x,rev newRhss)::newRules,next,rules))
	       end)
	      (IntListMap.empty,(nil,max+1,[(xDontCare,ruDontCare)])) rules
	      
            val newRules = rev newRules@rev newRules'
            val newStarts = map do_fexp starts

            val dfaVec = Vector.tabulate
               (TpDict.usedIndices tpDict,fn i => TpDict.getByIndex(tpDict,i))
            val berryVec = 
	      if !O_SHARE_RE then
		Vector.tabulate
		(ReDict.usedIndices reDict,fn i => 
		 (ReDict.getKey(reDict,i),ReDict.getByIndex(reDict,i)))
	      else
		Vector.fromList (rev (!reList))
		
         in (((next,newStarts,newRules),berryVec,dfaVec,xAttsContVars),(xDontCare,reDict,tpDict))
         end

      fun flatten args = #1(flatten' args)
   end

