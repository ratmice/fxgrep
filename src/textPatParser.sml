signature TextPatParser =
   sig
      val parseTextPattern : bool -> Errors.Position * UniChar.Vector -> GramData.TextPattern
   end

structure TextPatParser : TextPatParser =
   struct
      structure LrVals = TextPatLrValsFun(structure Token = LrParser.Token)
      structure Lex = TextPatLexer(structure Tokens = LrVals.Tokens)
      structure Parser = JoinWithArg(structure ParserData = LrVals.ParserData
				     structure Lex=Lex
				     structure LrParser=LrParser)

      open Parser GramData GrepError GramUtil

      (*---------------------------------------------------------------------*)
      (* the dummy function: int -> string is required by ml-yacc as the 1st *)
      (* argument to makeLexer (cf. patLexer.sml).                           *)
      (*---------------------------------------------------------------------*)
      fun parseTextPattern exact (pos,cv) =
         let 
	    val lexer = makeLexer (fn _ => "") cv
            val (res,_) = parse(15,lexer,yaccTpError pos,())
         in 
            case res
	      of NONE => TXT_UNDER
	       | SOME txtpat => if exact then txtpat 
                                else makeSeq [TXT_UNDER,txtpat,TXT_UNDER]
         end
   end
