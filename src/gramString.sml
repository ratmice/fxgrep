signature GramString = 
  sig
    val CharPattern2String    : GramData.CharPattern -> string
    val TextPattern2String    : GramData.TextPattern -> string
    val GiPattern2xString     : (int -> string) -> GramData.GiPattern -> string
    val AttPat2xString        : (int -> string) -> GramData.AttPat -> string
    val AttPattern2xString    : (int -> string) -> GramData.AttPattern -> string
    val XRegExp2xString       : (int -> string) -> GramData.XRegExp -> string
    val ForestExp2xString     : (int -> string) -> GramData.ForestExp -> string
    val Rhs2xString           : (int -> string) * (int -> string) -> GramData.Rhs -> string
    val Grammar2xString       : (int -> string) * (int -> string) -> 
      (GramData.Grammar * GramData.MatchSpec) -> string
    val FlatExp2String        : (int -> GramData.XRegExp) -> GramData.FlatExp -> string
    val FlatRhs2xString       : (int -> GramData.XRegExp) -> (int -> string) -> GramData.FlatRhs -> string
    val FlatGrammar2xString   : (int -> GramData.XRegExp) -> (int -> string) * (int -> string) 
      -> GramData.FlatGrammar * GramData.MatchSpec -> string
      
    val XRegExp2String     : GramData.XRegExp -> string
    val ForestExp2String   : GramData.ForestExp -> string
    val Grammar2String     : GramData.Grammar * GramData.MatchSpec -> string
    val FlatGrammar2String : (int -> GramData.XRegExp) -> 
      GramData.FlatGrammar * GramData.MatchSpec -> string
      
    val Grammar2tdString     : GramTables.XTable * DocDtd.Dtd -> 
      GramData.Grammar * GramData.MatchSpec -> string
    val FlatGrammar2tdString : (int -> GramData.XRegExp) -> GramTables.XTable * DocDtd.Dtd -> 
      GramData.FlatGrammar * GramData.MatchSpec -> string
      
    val Pattern2xString : (int -> string) ->GramData.Pattern -> string
    val Pattern2dString : DocDtd.Dtd -> GramData.Pattern -> string
    val Pattern2String  : GramData.Pattern -> string
      
    val TreePattern2String : GramData.TreePattern -> string
  end

structure GramString : GramString =
  struct               
    open 
      UniChar CharRanges Errors 
      GramData GramTables GramUtil 
      DocDtd UtilList UtilString
      
    val THIS_MODULE = "GramString"
    val quote = #"'"
      
    fun isSpecial c = member c 
      [0wx24,0wx28,0wx29,0wx2A,0wx2B,0wx2E,0wx5B,0wx5C,0wx5D,0wx5E,0wx7C]
      
    fun CharPattern2String cp = 
      if cp=CP_WHITE then "~" 
      else if cp=CP_DOT then "." 
	   else case cp
	     of CP_POS cr => CharRange2xString ("[","","-","]") cr 
	   | CP_NEG cr => CharRange2xString ("[^","","-","]") cr 
	   | CP_START => "^"
	   | CP_END => "$"
    fun TextPattern2String tp = 
      if tp=TXT_UNDER then ""
      else if tp=TXT_WHITE then "~"
	   else RegExp2String CharPattern2String tp
	   
    fun AttPat2xString Att2String ap = 
      case ap 
	of AT_NAME att => Att2String att
      | AT_VALUE(att,tp) => Att2String att^
	  "="^quoteString quote (TextPattern2String tp)
    fun AttPattern2xString Att2String (sign,ap) =
      (if sign then "" else "!")^AttPat2xString Att2String ap
	 
    fun GiPattern2xString Elem2String gp =
      case gp
	of GI_POS nil => raise InternalError(THIS_MODULE,"GiPattern2String",
					     "empty element type list in GI_POS") 
      | GI_POS [el] => Elem2String el
      | GI_POS els => List2xString ("(","|",")") Elem2String els
      | GI_NEG is => 
	  (case is of 
	     nil => "_"
	   | [el] => "-"^Elem2String el
	   | els => List2xString ("-(","|",")") Elem2String els)
      | GI_REG tp => quoteString quote (TextPattern2String tp)
	    
    fun TagPattern2xString Elem2String (gp,aps) = List2xString 
      ("<"^GiPattern2xString Elem2String gp,"",">") 
      (fn ap => " "^AttPattern2xString Elem2String ap) 
      aps
      
    fun XRegExp2xString X2String xre = 
      if xre=XRE_WHITE then "~"
      else if xre=XRE_UNDER then "_"
	   else RegExp2String X2String xre
	     
    fun ForestExp2xString X2String = List2xString (""," && ","")
      (fn (sign,re) => (if sign then "" else "! ")^XRegExp2xString X2String re)
      
    fun Rhs2xString (X2String,Elem2String) rhs =
      case rhs 
	of RHS_TEXT tp => "\""^TextPattern2String tp^"\""
      | RHS_PI(target,fe) => 
	  "<?"^TextPattern2String target^"?> "^ForestExp2xString X2String fe
      | RHS_TREE (tag,fe) => 
	  TagPattern2xString Elem2String tag^" "^
	  ForestExp2xString X2String fe
	  
    fun Grammar2xString (pars as (X2String,Elem2String)) 
      ((_,fes,rules),((form1,targets1),secondaries):GramData.MatchSpec) = 
      String.concat [List2xString ("Grammar: \n  Start:","","\n  Formula:") 
		     (fn rhs => "\n    "^ForestExp2xString X2String rhs) fes,
		     "\n    ",Formula.Formula2String X2String form1,
		     List2xString ("\n  Primaries:\n    "," ","") X2String targets1,
		     List2xString ("\n  Secondaries:\n    ","\n    ","")
		     (fn (form2,t) => 
		      "Formula: "^(Formula.Formula2String X2String form2)^"\n"^
                      "    Secondaries: "^ (List2xString (""," ","") X2String t)^"\n")
		     secondaries,
		     List2xString ("\n  Rules:","","") 
		     (fn (x,rhss) => List2xString ("","","")
		      (fn rhs => "\n    "^X2String x^" -> "^Rhs2xString pars rhs) rhss)
		     rules,
		     "\n\n"]
      
    fun FlatExp2String int2RegExp fe = List2xString (""," && ","")
      (fn (sign,re) => (if sign then "" else "! ")^(XRegExp2xString Int.toString (int2RegExp re))) fe
      
    fun FlatRhs2xString int2RegExp Elem2String rhs =
      case rhs 
	of FLAT_TEXT tp => "\""^(Int.toString (valOf tp) handle Option => "_")^"\""
      | FLAT_ELEM (gp,fe) => String.concat
	  ["<",GiPattern2xString Elem2String gp,">",FlatExp2String int2RegExp fe]
	  
    fun FlatGrammar2xString int2RegExp (pars as (X2String,Elem2String)) 
      ((_,fes,rules),((form1,targets1),secondaries)) = 
      String.concat [List2xString ("Flat Grammar: \n  Start:","","\n  Matches:") 
		     (fn rhs => "\n    "^FlatExp2String int2RegExp rhs) fes,
		     "\n    ",Formula.Formula2String X2String form1,
		     List2xString ("\n    Primaries"," ","") Int.toString targets1, 
		     List2xString ("\n    Secondaries:\n    ","\n    ","")
		     (fn (form2,t) => 
		      (Formula.Formula2String X2String form2)^"\n"^
		      (List2xString (""," ","") Int.toString t)^"\n")
		     secondaries,
		     List2xString ("\n    Rules:","","") 
		     (fn (x,rhss) => 
		      List2xString ("","","")
		      (fn rhs => "\n    "^Int.toString x^" -> "
		       ^FlatRhs2xString int2RegExp Elem2String rhs) rhss)
		     rules,
		     "\n\n"]

    fun Grammar2tdString (tab,dtd) g = Grammar2xString 
      (X2xString tab,DocElem2xString dtd) g
    fun FlatGrammar2tdString int2RegExp (tab,dtd) g = FlatGrammar2xString int2RegExp
      (X2xString tab,DocDtd.DocElem2xString dtd) g
      
    fun XRegExp2String re = XRegExp2xString X2String re
    fun Rhs2String tab re = XRegExp2xString X2String re
    fun ForestExp2String re = ForestExp2xString X2String re
    fun Grammar2String g = Grammar2xString (X2String,DocDtd.DocElem2String) g
    fun FlatGrammar2String int2RegExp g = FlatGrammar2xString int2RegExp (X2String,DocDtd.DocElem2String) g
      
    fun NodeTest2xString Elem2String nt = 
      case nt 
	of NT_TRUE => "."
      | NT_GI gp => GiPattern2xString Elem2String gp 
      | NT_TEXT tp => if tp=TXT_UNDER then "\"\"" else "\""^TextPattern2String tp^"\"" 
      | NT_PI tp => if tp=TXT_UNDER then "<? ?>" else "<?"^TextPattern2String tp^"?>" 
	  
    and Qualifier2xString Elem2String q = 
      case q
	of Q_ATT ap => AttPat2xString Elem2String ap
      | Q_CHILDREN fp => ForestPattern2xString Elem2String fp
	  
    and ForestPattern2xString Elem2String fp = 
      let 
	fun doit prec fp =
	  if (isFP_UNDER fp) then "_"
	  else if (isFP_WHITE fp) then "~"
	       else case fp
		 of RE_NULL => "0"
	       | RE_EMPTY => ""
	       | RE_UNDER => "_"
	       | RE_BASIC tp => TreePattern2xString Elem2String tp
	       | RE_OPT fp => doit 3 fp^"?"
	       | RE_REP fp => doit 3 fp^"*"
	       | RE_PLUS fp => doit 3 fp^"+"
	       | RE_SEQ(fp1,fp2) => 
                           let val (lpar,rpar) = if prec<=2 then ("","") else ("(",")")
                           in lpar^doit 2 fp1^","^doit 2 fp2^rpar
                           end
	       | RE_ALT(fp1,fp2) => 
                           let val (lpar,rpar) = if prec<=1 then ("","") else ("(",")")
                           in lpar^doit 1 fp1^"|"^doit 1 fp2^rpar
                           end
      in 
	doit 0 fp
      end

    and IncompletePath2xString Elem2String ip =
      let
	fun doit prec ip =
	  case ip of 
	    RegExp1.RE_NULL => "0"
	  | RegExp1.RE_EMPTY => ""
	  | RegExp1.RE_UNDER => "_"
	  | RegExp1.RE_BASIC np => (TargetNodePattern2xString Elem2String np)^"/"
	  | RegExp1.RE_DEEP np => (TargetNodePattern2xString Elem2String np)^"//"
	  | RegExp1.RE_OPT ip => doit 3 ip^"?"
	  | RegExp1.RE_REP ip => doit 3 ip^"*"
	  | RegExp1.RE_PLUS ip => doit 3 ip^"+"
	  | RegExp1.RE_SEQ(ip1,ip2) => 
	      let val (lpar,rpar) = if prec<=2 then ("","") else ("(",")")
	      in lpar^doit 2 ip1^","^doit 2 ip2^rpar
	      end
	  | RegExp1.RE_ALT(ip1,ip2) => 
	      let val (lpar,rpar) = if prec<=1 then ("","") else ("(",")")
	      in lpar^doit 1 ip1^"|"^doit 1 ip2^rpar
	      end
      in
	doit 0 ip
      end
	
    and TreePattern2xString Elem2String tp =
      case tp of
	TP (direct,cp) =>
	  (if direct then "" else "//")^
	     CompletePath2xString Elem2String cp
      | HASH => "#"
	     
    and CompletePath2xString Elem2String cp = 
      case cp of 
	CP_NODE np => TargetNodePattern2xString Elem2String np
      | CP_COMPOSED (ip,np) => 
	  (IncompletePath2xString Elem2String ip)^
	  (TargetNodePattern2xString Elem2String np)
      | CP_OR(cp1,cp2) => 
	  (CompletePath2xString Elem2String cp1)^"||"^
	  (CompletePath2xString Elem2String cp2)
	  
    and NodePattern2xString Elem2String (_,nt,qs) = 
      NodeTest2xString Elem2String nt^
      List2xString ("","","") 
      (fn (sign,q) => "["^(if sign then "" else "!")^Qualifier2xString Elem2String q^"]") qs

    and TargetNodePattern2xString Elem2String (secondaryTarget,(_,nt,qs)) = 
      (if secondaryTarget then ";secondary Target;"
       else "")^
	 NodeTest2xString Elem2String nt^
	 List2xString ("","","") 
	 (fn (sign,q) => "["^(if sign then "" else "!")^Qualifier2xString Elem2String q^"]") qs
	 
    fun Pattern2xString Elem2String pats = 
      List2xString (""," || ","") 
      (fn (qs,(direct,(ips,np))) =>
       let 
	 val begin = if (List.length ips) > 0 then ""
		     else if direct then "/"
			  else "//"
	 val spp = 
	   (List2xString ("","&","") 
	    (fn (direct,(negated,ip)) =>
	     (if negated then "!" else "")^
		(if direct then "/" else "//")^
		   (IncompletePath2xString Elem2String ip))
	    ips)^
	   (TargetNodePattern2xString Elem2String np)
	 val qs = List2xString ("","","") 
	   (fn (sign,q) => "["^(if sign then "" else "!")
	    ^ForestPattern2xString Elem2String q^"]") qs
       in 
	 qs^begin^spp
       end)
      pats
         
    val Pattern2String = Pattern2xString DocDtd.DocElem2String
    val TreePattern2String = TreePattern2xString DocDtd.DocElem2String
    fun Pattern2dString dtd = Pattern2xString (DocDtd.DocElem2xString dtd)

  end
