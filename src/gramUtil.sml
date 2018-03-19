signature GramUtil =
   sig
      val Rules     : UniChar.Data
      val Start     : UniChar.Data
      val Targets   : UniChar.Data
      val Prim      : UniChar.Data
                    
      val CP_DOT    : GramData.CharPattern
      val CP_NULL   : GramData.CharPattern
      val CP_WHITE  : GramData.CharPattern
                    
      val TXT_UNDER : GramData.TextPattern
      val TXT_WHITE : GramData.TextPattern
                    
      val auxGis    : int list
                    
      val GI_UNDER  : GramData.GiPattern
      val GI_DOT    : GramData.GiPattern
      val GI_WHITE  : GramData.GiPattern
      val GI_PI     : GramData.GiPattern
      val GI_ATTS   : GramData.GiPattern
      val GI_CONT   : GramData.GiPattern
      val GI_TARGET : GramData.GiPattern
                    
      val TAG_UNDER : GramData.TagPattern
      val TAG_DOT   : GramData.TagPattern
      val TAG_WHITE : GramData.TagPattern

      val NP_TRUE   : Errors.Position -> GramData.NodePattern
      val NP_WHITE  : Errors.Position -> GramData.NodePattern
      val NP_PI     : Errors.Position -> GramData.NodePattern

      val CPat_TRUE   : Errors.Position -> GramData.CompletePath
      val CPat_WHITE  : Errors.Position -> GramData.CompletePath
      val CPat_PI     : Errors.Position -> GramData.CompletePath
         
      val TP_TRUE   : Errors.Position -> GramData.TreePattern
      val isTP_TRUE   : GramData.TreePattern -> bool
      val TP_WHITE  : Errors.Position -> GramData.TreePattern
      val isTP_WHITE  : GramData.TreePattern -> bool

      val FP_UNDER  : Errors.Position -> GramData.ForestPattern
      val isFP_UNDER  : GramData.ForestPattern -> bool
      val FP_WHITE  : Errors.Position -> GramData.ForestPattern
      val isFP_WHITE  : GramData.ForestPattern -> bool

      val sortInt            : int list -> int list
      val sortIntPair        : (int * int) list -> (int * int) list

      val hashAttPat         : GramData.AttPat -> word
      val hashGiPattern      : GramData.GiPattern -> word
      val hashCharPattern    : GramData.CharPattern -> word
      val hashTextPattern    : GramData.TextPattern -> word

      val compareAttPat      : GramData.AttPat * GramData.AttPat -> order
      val compareGiPattern   : GramData.GiPattern * GramData.GiPattern -> order
      val compareCharPattern : GramData.CharPattern * GramData.CharPattern -> order
      val compareTextPattern : GramData.TextPattern * GramData.TextPattern -> order

      val compareNodePattern : GramData.NodePattern * GramData.NodePattern -> order
      val compareTargetNodePattern : GramData.TargetNodePattern * GramData.TargetNodePattern -> order

      val compareTreePattern : GramData.TreePattern * GramData.TreePattern -> order
   end

structure GramUtil : GramUtil =
   struct
      open CharRanges GramData DocDtd UtilCompare UtilHash UtilList UniChar

      val Rules   = String2Data "RULES"
      val Start   = String2Data "START"
      val Targets = String2Data "TARGETS"
      val Prim = String2Data "FORMULA"

      (*--------------------------------------------------------------------*)
      (* arbitrary character.                                               *)
      (*--------------------------------------------------------------------*)
      val wsRange  = Data2CharRange [0wx09,0wx0A,0wx0D,0wx20]
      val CP_DOT   = CP_NEG emptyCharRange
      val CP_NULL  = CP_POS emptyCharRange
      val CP_WHITE = CP_POS wsRange
      (*--------------------------------------------------------------------*)
      (* arbitrary text and white space.                                    *)
      (*--------------------------------------------------------------------*)
      val TXT_UNDER = RE_REP(RE_BASIC CP_DOT)
      val TXT_WHITE = makeSeq [RE_BASIC CP_START,RE_REP(RE_BASIC CP_WHITE),RE_BASIC CP_END]
      (*--------------------------------------------------------------------*)
      (* arbitrary element type except for #pi / including #pi.             *) 
      (*--------------------------------------------------------------------*)
      val auxGis = sort Int.compare [piIdx,attrsIdx,contentIdx,targetIdxE] 
      val GI_UNDER = GI_NEG nil
      val GI_DOT   = GI_NEG auxGis
      val GI_PI    = GI_POS [piIdx]
      val GI_WHITE = GI_POS [piIdx]
      val GI_ATTS  = GI_POS [attrsIdx]
      val GI_CONT  = GI_POS [contentIdx]
      val GI_TARGET= GI_POS [targetIdxE]
      (*--------------------------------------------------------------------*)
      (* tag pattern for arbitrary element types or white space.            *) 
      (*--------------------------------------------------------------------*)
      val TAG_UNDER = (GI_UNDER,nil)
      val TAG_DOT   = (GI_DOT,nil)
      val TAG_WHITE = (GI_WHITE,nil)
      (*--------------------------------------------------------------------*)
      (* node pattern for arbitrary element types, white space and pi's.    *) 
      (*--------------------------------------------------------------------*)
      fun NP_TRUE  pos = (pos,NT_TRUE,nil)
      fun NP_WHITE pos = (pos,NT_TEXT TXT_WHITE,nil)
      fun NP_PI pos = (pos,NT_PI TXT_UNDER,nil)
      (*--------------------------------------------------------------------*)
      (* path pattern for arbitrary elements, white space and pi's.         *) 
      (*--------------------------------------------------------------------*)
      fun CPat_TRUE pos = CP_NODE (false,NP_TRUE pos)
      fun CPat_WHITE pos = CP_NODE (false,NP_WHITE pos)
      fun CPat_PI pos = CP_NODE (false,NP_PI pos)
      (*--------------------------------------------------------------------*)
      (* tree pattern for arbitrary elements, white space.                  *) 
      (*--------------------------------------------------------------------*)
      fun TP_TRUE  pos = TP (false,CPat_TRUE pos)
      fun isTP_TRUE tp = 
	case tp of 
	  TP (false,CP_NODE(false,(_,NT_TRUE,nil))) => true
	| _ => false
      fun TP_WHITE pos = TP (true,(CP_OR(CPat_WHITE pos,CPat_PI pos)))
      fun isTP_WHITE tp = 
	case tp of 
	  TP (true,(CP_OR(CP_NODE (false,(_,NT_TEXT TXT_WHITE,nil)),CP_NODE (false,(pos,NT_PI TXT_UNDER,nil))))) => true
	| _ => false
      (*--------------------------------------------------------------------*)
      (* forest pattern for arbitrary forests, white space.                 *) 
      (*--------------------------------------------------------------------*)
      fun FP_UNDER pos = RE_REP(RE_BASIC (TP_TRUE pos)) : ForestPattern
      fun isFP_UNDER fp = 
	case fp of 
	  RE_REP(RE_BASIC (TP (false,CP_NODE(false,(_,NT_TRUE,nil))))) => true
	| _ => false
      fun FP_WHITE pos = RE_REP(RE_BASIC (TP_WHITE pos)): ForestPattern
      fun isFP_WHITE fp = 
	case fp of 
	  RE_REP(RE_BASIC (TP (true,(CP_OR(CP_NODE (false,(_,NT_TEXT TXT_WHITE,nil)),CP_NODE (false,(pos,NT_PI TXT_UNDER,nil))))))) => true
	| _ => false

      (*--------------------------------------------------------------------*)
      (* hash a character pattern to a word.                                *)
      (*--------------------------------------------------------------------*)
      fun hashCharPattern CP_START = 0w0
        | hashCharPattern CP_END = 0w1
        | hashCharPattern (CP_POS cr) = 0w2 + 0w2 * hashCharRange cr
        | hashCharPattern (CP_NEG cr) = 0w3 + 0w2 * hashCharRange cr
      (*--------------------------------------------------------------------*)
      (* hash a text pattern to a word.                                     *)
      (*--------------------------------------------------------------------*)
      val hashTextPattern = hashRegExp hashCharPattern
      (*--------------------------------------------------------------------*)
      (* hash an attribute pattern to a word.                               *)
      (*--------------------------------------------------------------------*)
      fun hashAttPat ap = 
         case ap 
           of AT_NAME i => 0w2*hashInt i
            | AT_VALUE itp => 0w1+0w2*hashPair(hashInt,hashTextPattern) itp
      fun hashAttPattern (sign,ap) = if sign then hashAttPat ap else 0w0-(hashAttPat ap)
      (*--------------------------------------------------------------------*)
      (* hash a gi pattern to a word.                                       *)
      (*--------------------------------------------------------------------*)
      fun hashGiPattern (GI_REG tp)  = 0w3 * hashTextPattern tp
        | hashGiPattern (GI_NEG els) = 0w1 +0w3 * hashList Word.fromInt els
	| hashGiPattern (GI_POS els) = 0w2 + 0w3 * hashList Word.fromInt els

      (*--------------------------------------------------------------------*)
      (* compare two character patterns.                                    *)
      (*--------------------------------------------------------------------*)
      fun compareCharPattern cps = 
         case cps
           of (CP_START  ,CP_START  ) => EQUAL
            | (CP_START  ,_         ) => LESS
            | (_         ,CP_START  ) => GREATER
            | (CP_END    ,CP_END    ) => EQUAL
            | (CP_END    ,_         ) => LESS
            | (_         ,CP_END    ) => GREATER
            | (CP_POS cr1,CP_POS cr2) => compareCharRange(cr1,cr2)
            | (CP_POS _  ,_         ) => LESS
            | (_         ,CP_POS _  ) => GREATER
            | (CP_NEG cr1,CP_NEG cr2) => compareCharRange(cr1,cr2)
      (*--------------------------------------------------------------------*)
      (* compare two text patterns.                                         *)
      (*--------------------------------------------------------------------*)
      val compareTextPattern = compareRegExp compareCharPattern
      (*--------------------------------------------------------------------*)
      (* compare two attribute patterns.                                    *)
      (*--------------------------------------------------------------------*)
      fun compareAttPat aps = 
         case aps
           of (AT_NAME i,AT_NAME j) => Int.compare(i,j)
            | (AT_NAME _,_) => LESS
            | (_,AT_NAME _) => GREATER
            | (AT_VALUE ics1,AT_VALUE ics2) => 
              comparePair (Int.compare,compareTextPattern) (ics1,ics2)
      fun compareAttPattern((s1,ap1),(s2,ap2)) =
         if s1=s2 then compareAttPat (ap1,ap2)
         else if s1 then GREATER else LESS
      (*--------------------------------------------------------------------*)
      (* compare two gi patterns.                                           *)
      (*--------------------------------------------------------------------*)
      fun compareGiPattern gps =
         case gps
           of (GI_POS els1,GI_POS els2) => compareList Int.compare(els1,els2)
            | (GI_POS _,   _   ) => LESS
            | (GI_NEG _,   GI_POS _   ) => GREATER
            | (GI_NEG els1,GI_NEG els2) => compareList Int.compare(els1,els2)
	    | (GI_NEG _, GI_REG _) => LESS
            | (GI_REG regexp1, GI_REG regexp2) => compareTextPattern (regexp1,regexp2)
            | (GI_REG _, _) => GREATER

      fun compareBool (b1,b2) =
	case (b1,b2) of
	  (true,false) => GREATER
	| (false,true) => LESS
	| _ => EQUAL

      fun compareNodeTest nt12 = 
         case nt12 
           of (NT_TRUE,NT_TRUE) => EQUAL
            | (NT_TRUE,_) => LESS
            | (_,NT_TRUE) => GREATER
            | (NT_GI gp1,NT_GI gp2) => compareGiPattern(gp1,gp2)
            | (NT_GI _,_) => LESS
            | (_,NT_GI _) => GREATER
            | (NT_TEXT tp1,NT_TEXT tp2) => compareTextPattern(tp1,tp2)
            | (NT_TEXT _,_) => LESS
            | (_,NT_TEXT _) => GREATER
            | (NT_PI tp1,NT_PI tp2) => compareTextPattern(tp1,tp2)

      and compareQualifier q12 = 
         case q12
           of (Q_ATT ap1,Q_ATT ap2) => compareAttPat(ap1,ap2)
            | (Q_ATT _,_) => LESS
            | (_,Q_ATT _) => GREATER
            | (Q_CHILDREN fp1,Q_CHILDREN fp2) => compareForestPattern(fp1,fp2)

      and compareForestPattern fp12 = 
         compareRegExp compareTreePattern fp12

      and compareIncompletePath ip12 =
	RegExp1.compareRegExp compareTargetNodePattern ip12

      and compareSignedIncompletePath sip12 =
	comparePair (compareBool,compareIncompletePath) sip12

      and compareNodePattern ((_,nt1,q1),(_,nt2,q2)) =
	comparePair
	(compareNodeTest,compareList 
	 (fn((s1,q1),(s2,q2)) => if s1=s2 then compareQualifier (q1,q2)
				 else (if s1 then GREATER else LESS))) 
	((nt1,q1),(nt2,q2))

      and compareTargetNodePattern nps = 
	comparePair 
	(
	 (fn (x,y) => 
	  if x=y then EQUAL
	  else if x then GREATER
	       else LESS),
	 compareNodePattern
	 ) nps
	 
      and compareCompletePath (cp1,cp2) =
	case (cp1,cp2) of
	  (CP_NODE np1,CP_NODE np2) => compareTargetNodePattern(np1,np2)
	| (CP_NODE _,_) => LESS
	| (_,CP_NODE _) => GREATER
	| (CP_OR cps1,CP_OR cps2) => comparePair
	    (compareCompletePath,compareCompletePath) (cps1,cps2)
	| (CP_OR _,_) => LESS
	| (_,CP_OR _) => GREATER
	| (CP_COMPOSED ipnp1,CP_COMPOSED ipnp2) => comparePair
	    (compareIncompletePath,compareTargetNodePattern) (ipnp1,ipnp2)

      and compareTreePattern (tp1,tp2)=
	case (tp1,tp2) of
	  (TP(s1,cp1),TP(s2,cp2)) =>
	    if s1=s2 then compareCompletePath(cp1,cp2)
	    else if s1 then GREATER else LESS
	| (TP _,_) => LESS
	| (_,TP _) => GREATER
	| (HASH,HASH) => EQUAL
            
      (*--------------------------------------------------------------------*)
      (* sort a list of attribute patterns.                                 *)
      (*--------------------------------------------------------------------*)
      val sortInt = sort Int.compare
      val sortIntPair = UtilList.sort (UtilCompare.comparePair(Int.compare,Int.compare))
   end