signature GrammarParser =
   sig
      exception ParseError

      val parseRule : DocDtd.Dtd * GramTables.XTable 
	 -> Errors.Position * GramData.Input -> GramData.Rhs
      val parseFexp : DocDtd.Dtd * GramTables.XTable 
	 -> Errors.Position * GramData.Input -> GramData.ForestExp
      val parseTargets : DocDtd.Dtd * GramTables.XTable 
	 -> Errors.Position * GramData.Input -> int list
      val parseFormula : DocDtd.Dtd * GramTables.XTable 
	 -> Errors.Position * GramData.Input -> int Formula.Formula

      val parseGrammar : DocDtd.Dtd * GramTables.XTable 
	 -> Uri.Uri -> GramData.Grammar * GramData.MatchSpec
   end

structure GrammarParser : GrammarParser =
   struct
      structure LrVals = GrammarLrValsFun(structure Token = LrParser.Token)
      structure Lex = GrammarLexer(structure Tokens = LrVals.Tokens)
      structure Parser = JoinWithArg(structure ParserData = LrVals.ParserData
				     structure Lex=Lex
				     structure LrParser=LrParser)
      structure FileLex = GrammarFileLexer(structure Tokens = LrVals.Tokens)
      structure FileParser = JoinWithArg(structure ParserData = LrVals.ParserData
                                         structure Lex=FileLex
                                         structure LrParser=LrParser)
         
      open LrVals.Tokens GramData GrepError Uri UtilError

      val THIS_MODULE = "GrammarParser"

      exception ParseError = Parser.ParseError

      local 
         open Parser
      in 
         (*---------------------------------------------------------------------*)
         (* the dummy function: int -> string is required by ml-yacc as the 1st *)
         (* argument to makeLexer (cf. patLexer.sml).                           *)
         (* the dummy token (PTX_RULE, PTX_FEXP or PTX_TARGETS) selects         *)
         (* whether the grammar produces right ahd sides, forest expressions    *)
         (* lists of target variables.                                          *)
         (* This is a wa of using the same grammar for all three alternatives.  *)
         (*---------------------------------------------------------------------*)
         fun parseSomething (dtd,tab) (pos,input) (desc,tok) =
            let 
               val lexer = makeLexer (fn _ => "") (desc,pos,input)
               val lexer1 = Stream.cons(tok(pos,pos),lexer)
               val (res,_) = parse(15,lexer1,yaccError desc,(dtd,tab))
            in res
            end
         fun parseRule (dtd,tab) (pos,input) =
            case parseSomething (dtd,tab) (pos,input) ("grammar rule",PTX_RULE)
              of Y_RULE rhs => rhs
               | _ => raise ParseError
         fun parseFexp (dtd,tab) (pos,input) =
            case parseSomething (dtd,tab) (pos,input) ("start expression",PTX_FEXP)
              of Y_FEXP fe => fe
               | _ => raise ParseError
         fun parseTargets (dtd,tab) (pos,input) =
            case parseSomething (dtd,tab) (pos,input) ("target variable list",PTX_TARGET)
              of Y_TARGET fe => fe
               | _ => raise ParseError
         fun parseFormula (dtd,tab) (pos,input) =
            case parseSomething (dtd,tab) (pos,input) ("formula",PTX_FORM)
              of Y_FORM f => f
               | _ => raise ParseError
      end

      local 
         open Errors FileParser
      in 
         fun parseGrammar (dtd,tab) uri =
            let 
               val pos0 = (Uri2String uri,0,0)
               val lexer = makeLexer (fn _ => "") uri
                  handle NoSuchFile fmsg => 
                     let val _ = printError "grammar " (nullPosition,ERR_NO_SUCH_FILE fmsg)
                     in raise ParseError
                     end
               val lexer1 = Stream.cons(PTX_GRAMMAR(pos0,pos0),lexer)
               val (res,_) = parse(15,lexer1,yaccError "grammar",(dtd,tab))
            in case res 
                 of Y_GRAMMAR g => g
                  | _ => raise ParseError
            end
      end
   end

