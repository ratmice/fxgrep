functor FilePatternLexer (structure Tokens : Pattern_TOKENS) : ARG_LEXER =
  struct
    structure PatternLexer = 
      PatternLexer
      (structure Tokens = Tokens
       type State = GrammarFile.File
       val get = GrammarFile.getChar
       val getPos = GrammarFile.getPos
       val getPP = 
	 fn q => let 
		   val pos = getPos q 
		 in 
		   (pos,pos) 
		 end
       val errorBadChar = GrepError.errorBadChar "grammar"
       val errorUnclosed = GrepError.errorUnclosed "grammar")
	 
    structure UserDeclarations = 
      struct 
	type pos = Errors.Position
	type svalue = Tokens.svalue
	type ('a,'b) token = ('a,'b) Tokens.token 
	type arg = Uri.Uri
      end
    
     (*---------------------------------------------------------------------*)
     (* ml-yacc requires the first argument of makeLexer to be a function   *)
     (* that reads characters. this argument is ignored since we deal with  *)
     (* segments of XML input given - together with extra information - in  *)
     (* the second argument.                                                *)
     (*---------------------------------------------------------------------*)
     fun makeLexer _ uri = 
       let 
	 val q = ref (GrammarFile.openFile uri)
       in
	 PatternLexer.makeLexer q
       end
   end
