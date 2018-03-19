signature PatternParser =
  sig
    exception ParseError
    
    val parsePattern: DocDtd.Dtd -> GramData.PatSpec' -> GramData.Pattern
    val parseUniCharVectorPattern : DocDtd.Dtd -> Errors.Position * UniChar.Vector -> GramData.Pattern
  end

structure PatternParser : PatternParser = 
   struct
      structure LrVals = PatternLrValsFun(structure Token = LrParser.Token)
      structure Lex = CommandLinePatternLexer(structure Tokens = LrVals.Tokens)
      structure Parser = JoinWithArg(structure ParserData = LrVals.ParserData
				     structure Lex=Lex
				     structure LrParser=LrParser)

      structure FileLex = FilePatternLexer(structure Tokens = LrVals.Tokens)
      structure FileParser = JoinWithArg(structure ParserData = LrVals.ParserData
                                         structure Lex=FileLex
                                         structure LrParser=LrParser)
         
      exception ParseError = Parser.ParseError

      open Errors GramData

      fun parseUniCharVectorPattern dtd (pos,vec) =
	let
	  val input = [GramData.SEG_DATA(vec,pos)]
	  val lexer = Parser.makeLexer (fn _ => "") (pos,input)
	  val (p,_) = Parser.parse(15,lexer,GrepError.yaccError "pattern",dtd)
	in 
	  p
	end

      fun parsePattern dtd spec =
         case spec
           of STR str => let val pos = ("<cmdline arg>",1,0)
                             val input = [GramData.SEG_DATA(UniChar.String2Vector str,pos)]
                             val lexer = Parser.makeLexer (fn _ => "") (pos,input)
                             val (p,_) = Parser.parse(15,lexer,GrepError.yaccError "pattern",dtd)
                         in p
                         end
            | URI uri => let val lexer = FileParser.makeLexer (fn _ => "") uri
                             val (p,_) = FileParser.parse
                                (15,lexer,GrepError.yaccError "pattern",dtd)
                         in p
                         end
                      handle NoSuchFile fmsg => 
                         let val _ = GrepError.printError "pattern " 
                            (nullPosition,ERR_NO_SUCH_FILE fmsg)
                         in raise ParseError
                         end
   end
