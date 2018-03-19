signature GramParse = 
  sig
    exception ParseError

    val parseGrammar : GramData.PatSpec -> DocDtd.Dtd * GramTables.XTable * 
      (GramData.Grammar * GramData.MatchSpec)
  end

structure GramParse : GramParse =
  struct
    structure ParseGrammar = Parse (structure Dtd = GrammarDtd0
				    structure Hooks = GramHooks0
				    structure Resolve = GrepResolve
				    structure ParserOptions = GramOptions)
	 
    open 
      DocDtd GramData GramOptions GramTables GrepError Uri

    exception ParseError = GrammarParser.ParseError

    (*---------------------------------------------------------------------*)
    (* check for each variable whether it has at least one rule.           *)
    (*---------------------------------------------------------------------*)
    fun checkUndefined tab ((_,_,rules),_) = app 
      (fn (x,rhs) => case rhs
       of nil => warnUndefined (getRefs tab x,Index2X tab x) 
     | _ => ()) 
      rules

    fun readGrammar (dtd,tab) uri = 
      let 
	(*---------------------------------------------------------------*)
	(* the toplevel must handle Option in order to recognize that no *)
	(* pattern was specified. It must also handle ParseError to find *)
	(* out about syntax errors.                                      *)
	(*---------------------------------------------------------------*)
	val suffix = uriSuffix uri 
	val g = if suffix="xml" orelse suffix="XML" 
		  then ParseGrammar.parseDocument 
		    (SOME uri) NONE ((*GrammarHooks*)GramHooks.grammarStart(dtd,tab))
		else GrammarParser.parseGrammar (dtd,tab) uri 
      in g
      end

    fun readPattern (dtd,tab) spec = 
      let 
	val pat = PatternParser.parsePattern dtd spec
	(*---------------------------------------------------------------*)
	(*  now convert the pattern into a grammar                       *)
	(*---------------------------------------------------------------*)
	val g = PatGrammar.Pattern2Grammar tab pat
      (*val _ = print (GramString.Grammar2tdString (tab,dtd) g)*)
      in g
      end

      
    fun parseGrammar spec = 
      let 
	val _ = initGramError()
	val tab = initXTable()
	val dtd = initDocDtd() 
(* used when parsing start expressions, targets, etc. and then when matching *)

	(*-------------------------------------------------------*)
	(* depending on input spec, parse a grammar or a pattern *)
	(*-------------------------------------------------------*)
	val g = 
	  case spec of 
	    PATTERN s => readPattern (dtd,tab) s
	  | GRAMMAR uri => readGrammar (dtd,tab) uri

	(*---------------------------------------------------------------*)
	(* the toplevel handles ParseError, so we can use it for         *)
	(* indicating syntax errors and xml errors.                      *)
	(*---------------------------------------------------------------*)
	val _ = if !hadXmlError andalso not (!O_IGNORE_XML_ERRORS) 
		  then raise ParseError else ()
	val _ = if !hadSyntaxError andalso not (!O_IGNORE_SYNTAX_ERRORS) 
		  then raise ParseError else ()

	(*-------------------------------------------------------*)
	(* possibly do some debugging output                     *)
	(*-------------------------------------------------------*)
	val _ = if !O_GREP_DEBUG<=1 then ()
		else 
		  let 
		    val ((max,start,rules),(targets1,targets2)) = g
		    val Int2String = (StringCvt.padLeft #" " 6) o Int.toString
		  in app print 
		       ["Grammar:\n  ",
			Int2String max," variables\n  ",
			Int2String 
			(foldr (fn ((_,rhs),r) => r+length rhs) 0 rules)," rules.\n\n"]
		     end

	(*val _ =  print (GramString.Grammar2tdString (tab,dtd) g)*)

	(*---------------------------------------------------------------*)
	(* now check for undefined variables                             *)
	(*---------------------------------------------------------------*)
	val _ = checkUndefined tab g
      in 
	(dtd,tab,g)
      end
  end
