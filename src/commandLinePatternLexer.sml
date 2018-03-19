functor CommandLinePatternLexer (structure Tokens : Pattern_TOKENS) : ARG_LEXER =
   struct
     structure PatternLexer = 
       PatternLexer
       (structure Tokens = Tokens
	type State = Errors.Position * GramData.Input
	val get =
	  let
	    fun incCol(f,l,c) = (f,l,c+1)
	    fun incLine(f,l,c) = (f,l+1,0)
	      
	    fun get (q as (pos,segs)) =
	      case segs 
		of nil => (0wx0,q)
	      | seg::segs => 
		  case seg of 
		    GramData.SEG_CREF (c,p)   => (c,(p,segs))
		  | GramData.SEG_OTHER p     => get(p,segs)
		  | GramData.SEG_DATA (cv,p)  => 
		      get (p,GramData.SEG_CURRENT(cv,Vector.length cv,0)::segs)
		  | GramData.SEG_CDATA (cv,p) => 
		      get(p,GramData.SEG_CURRENT(cv,Vector.length cv,0)::segs)
		  | GramData.SEG_CURRENT (cv,s,i) => 
		      if i>=s then get (pos,segs) 
		      else 
			let 
			  val c = Vector.sub(cv,i)
			  val newPos = if c=0wx0A then incLine pos else incCol pos
			in 
			  (c,(newPos,GramData.SEG_CURRENT(cv,s,i+1)::segs))
			end
	  in
	    get
	  end
	val getPos = fn (pos,_) => pos
	val getPP = fn (pos,_) => (pos,pos)
	val errorBadChar = GrepError.errorBadChar "pattern"
	val errorUnclosed = GrepError.errorUnclosed "pattern")

     structure UserDeclarations = 
       struct 
	 type pos = Errors.Position
	 type svalue = Tokens.svalue
	 type ('a,'b) token = ('a,'b) Tokens.token 
	 type arg = pos * GramData.Input
       end

     (*---------------------------------------------------------------------*)
     (* ml-yacc requires the first argument of makeLexer to be a function   *)
     (* that reads characters. this argument is ignored since we deal with  *)
     (* segments of XML input given - together with extra information - in  *)
     (* the second argument.                                                *)
     (*---------------------------------------------------------------------*)
     fun makeLexer _ (pos0,segs) = 
       let 
	 val q = ref (pos0,segs)
       in 
	 PatternLexer.makeLexer q
       end
   end

