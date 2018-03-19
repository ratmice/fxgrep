functor GrammarLexer (structure Tokens : Grammar_TOKENS) : ARG_LEXER =
(* for when the grammar is given as an xml file *)
   struct
      open Errors GramData GrepError Tokens UniChar UniClasses 
	 
      structure UserDeclarations = 
	 struct 
	    type pos = Position
	    type svalue = Tokens.svalue
	    type ('a,'b) token = ('a,'b) Tokens.token 
	    type arg = string * pos * Input
	 end

      val errorBadChar = errorBadChar "grammar"
      val errorUnclosed = errorUnclosed "grammar"

      (*---------------------------------------------------------------------*)
      (* ml-yacc requires the first argument of makeLexer to be a function   *)
      (* that reads characters. this argument is ignored since we deal with  *)
      (* segments of XML input given - together with extra information - in  *)
      (* the second argument.                                                *)
      (*---------------------------------------------------------------------*)
      fun makeLexer _ (what,pos0,segs) = 
	 let 
	    type State = Errors.Position * Input

	    exception IllegalChar of State * Position * Char 
	    exception Unclosed of  State * Position * string
	    
	    val q = ref (pos0,segs)

	    fun incCol(f,l,c) = (f,l,c+1)
	    fun incLine(f,l,c) = (f,l+1,0)
	    fun getPos(pos,_) = pos
	    fun getPP (pos,_) = (pos,pos)

	    fun get (q as (pos,segs)) =
	       case segs 
		 of nil => (0wx0,q)
		  | seg::segs => 
		    case seg
		      of SEG_CREF(c,p)   => (c,(p,segs))
		       | SEG_OTHER p     => get(p,segs)
		       | SEG_DATA(cv,p)  => get(p,SEG_CURRENT(cv,Vector.length cv,0)::segs)
		       | SEG_CDATA(cv,p) => get(p,SEG_CURRENT(cv,Vector.length cv,0)::segs)
		       | SEG_CURRENT(cv,s,i) => 
			 if i>=s then get(pos,segs) 
			 else let val c = Vector.sub(cv,i)
				  val newPos = if c=0wx0A then incLine pos else incCol pos
			      in (c,(newPos,SEG_CURRENT(cv,s,i+1)::segs))
			      end

	    fun getName (last,q) = 
	       let val (c,q1) = get q
	       in if isName c 
		     then let val (cs,pos2,q2) = getName(q,q1)
			  in (c::cs,pos2,q2)
			  end
		  else (nil,getPos last,q)
	       end

	    fun getLit(pos0,quote,q) =
	       let 
		  fun doit(yet,q) = 
		     let 
		       val (c,q1) = get q
		     in 
		       case c of
			 0wx00 => raise Unclosed(q1,pos0,"literal")
		       | 0wx5C =>
			   let
			     val (c2,q2) = get q1
			   in
			     if c2=quote then doit (quote::yet,q2)
			     else doit (c2::c::yet,q2)
			   end
		       | _ =>
			   if c=quote then (Data2Vector(rev yet),getPos q,q1)
			   else doit(c::yet,q1)
		     end
	       in 
		 doit(nil,q)
	       end

	    fun getPi(pos0,q) =
	       let 
		  fun doit yet (c,q) = 
		     case c
			  of 0wx00 => raise Unclosed(q,pos0,"processing instruction")
			   | 0wx3F => let val (c1,q1) = get q
				      in if c1=0wx3E then (rev yet,q,q1)
					 else doit (c::yet) (c1,q1)
				      end
			   | _ => doit (c::yet) (get q)
	       
		  val (c1,q1) = get q
		  val (target0,qE,q2) = doit nil (c1,q1)
		  val target = Data2Vector target0
	       in 
		  ((getPos q,target),getPos qE,q2)
	       end

	    fun getToken q = 
	       let val (c,q1) = get q
	       in case c
		    of 0wx00 => (PT_EOT(getPP q),q1)
		     | 0wx09 => getToken q1
		     | 0wx0A => getToken q1
		     | 0wx0D => getToken q1
		     | 0wx20 => getToken q1
		     | 0wx21 => (PT_NOT(getPP q),q1)
		     | 0wx22 => let val pos1 = getPos q
				    val (lit,pos2,q2) = getLit(pos1,c,q1)
				in (PT_LIT(lit,pos1,pos2),q2)
				end
		     | 0wx24 => (PT_DOLLAR(getPP q),q1)
		     | 0wx26 => let val (c1,q2) = get q1
				in if c1=0wx26 then (PT_AND(getPos q,getPos q1),q2)
				   else (PT_AMPERSAND(getPP q),q1)
				end
		     | 0wx27 => let val pos1 = getPos q
				    val (lit,pos2,q2) = getLit(pos1,c,q1)
				in (PT_LIT(lit,pos1,pos2),q2)
				end
		     | 0wx28 => (PT_LPAR(getPP q),q1)
		     | 0wx29 => (PT_RPAR(getPP q),q1)
		     | 0wx2A => let val (c1,q2) = get q1
				in if c1=0wx2A then (PT_REPP(getPos q,getPos q1),q2)
				   else (PT_REP(getPP q),q1)
				end
		     | 0wx2B => let val (c1,q2) = get q1
				in if c1=0wx2B then (PT_PLUSS(getPos q,getPos q1),q2)
				   else (PT_PLUS(getPP q),q1)
				end
		     | 0wx2C => (PT_COMMA(getPP q),q1)
		     | 0wx2E => (PT_DOT(getPP q),q1)
		     | 0wx3C => let val (c1,q2) = get q1
				in if c1=0wx3F 
                                      then let val pos1 = getPos q
                                               val (pi,pos2,q3) = getPi(pos1,q2)
                                           in (PT_PI(pi,pos1,pos2),q3)
                                           end
                                   else (PT_STAGO(getPP q),q1)
				end
		     | 0wx3D => (PT_EQ(getPP q),q1)
		     | 0wx3E => (PT_TAGC(getPP q),q1)
		     | 0wx3F => (PT_OPT(getPP q),q1)
		     | 0wx5E => (PT_HAT(getPP q),q1)
		     | 0wx5F => (PT_UNDER(getPP q),q1)
		     | 0wx7C => let val (c1,q2) = get q1
				in if c1=0wx7C then (PT_OR(getPos q,getPos q1),q2)
				   else (PT_ALT(getPP q),q1)
				end

		     | 0wx7E => (PT_TILDE(getPP q),q1)
		     | _     => if isNms c then let val (cs,pos2,q2) = getName (q,q1)
						in (PT_NAME(c::cs,getPos q,pos2),q2)
						end
				else raise IllegalChar(q1,getPos q,c)
	       end

	    fun nextToken() = 
	       let val (tok,q1) = getToken(!q)
	       in tok before q := q1 
	       end
	    handle IllegalChar(q1,pos,c) => let val _ = errorBadChar pos c
                                                val _ = q := q1
                                            in nextToken()
                                            end
		 | Unclosed(q1,p,what) => let val _ = errorUnclosed (getPos q1,p) what
					      val _ = q := q1
					  in nextToken()
					  end
	 in nextToken
	 end
   end

functor GrammarFileLexer (structure Tokens : Grammar_TOKENS) : ARG_LEXER =
(* for when the grammar is given as a file which is not an xml file *)
   struct
      open Errors GramData GrepError GrammarFile GramUtil Tokens UniChar UniClasses 
	 
      structure UserDeclarations = 
	 struct 
	    type pos = Position
	    type svalue = Tokens.svalue
	    type ('a,'b) token = ('a,'b) Tokens.token 
	    type arg = Uri.Uri
         end

      val errorBadChar = errorBadChar "grammar"
      val errorUnclosed = errorUnclosed "grammar"

      (*---------------------------------------------------------------------*)
      (* ml-yacc requires the first argument of makeLexer to be a function   *)
      (* that reads characters. this argument is ignored since we deal with  *)
      (* segments of XML input given - together with extra information - in  *)
      (* the second argument.                                                *)
      (*---------------------------------------------------------------------*)
      fun makeLexer _ uri = 
	 let 
	    type State = File
	    val q = ref (openFile uri)

	    exception IllegalChar of State * Position * Char
	    exception Unclosed of State * Position * string
	    
	    val get = getChar
	    fun getPP q = let val pos = getPos q in (pos,pos) end

	    fun getName (last,q) = 
	       let val (c,q1) = get q
	       in if isName c 
		     then let val (cs,pos2,q2) = getName(q,q1)
			  in (c::cs,pos2,q2)
			  end
		  else (nil,getPos last,ungetChar(q1,c))
	       end

	    fun getLit(pos0,quote,q) =
	       let 
		  fun doit(yet,q) = 
		     let 
		       val (c,q1) = get q
		     in 
		       case c of
			 0wx00 => raise Unclosed(q1,pos0,"literal")
		       | 0wx5C =>
			   let
			     val (c2,q2) = get q1
			   in
			     if c2=quote then doit (quote::yet,q2)
			     else doit (c2::c::yet,q2)
			   end
		       | _ =>
			   if c=quote then (Data2Vector(rev yet),getPos q,q1)
			   else doit(c::yet,q1)
		     end
	       in 
		 doit(nil,q)
	       end

	    fun getPi(pos0,q) =
	       let 
		  fun doit yet (c,q) = 
		     case c
			  of 0wx00 => raise Unclosed(q,pos0,"processing instruction")
			   | 0wx3F => let val (c1,q1) = get q
				      in if c1=0wx3E then (rev yet,q,q1)
					 else doit (c::yet) (c1,q1)
				      end
			   | _ => doit (c::yet) (get q)
	       
		  val (c1,q1) = get q
		  val (target0,qE,q2) = doit nil (c1,q1)
		  val target = Data2Vector target0
	       in 
		  ((getPos q,target),getPos qE,q2)
	       end

	    fun getToken q = 
	       let val (c,q1) = get q
	       in case c
		    of 0wx00 => (PT_EOT(getPP q),q1)
		     | 0wx09 => getToken q1
		     | 0wx0A => (PT_NL(getPP q),q1)
		     | 0wx0D => getToken q1
		     | 0wx20 => getToken q1
		     | 0wx21 => (PT_NOT(getPP q),q1)
		     | 0wx22 => let val pos1 = getPos q
				    val (lit,pos2,q2) = getLit(pos1,c,q1)
				in (PT_LIT(lit,pos1,pos2),q2)
				end
		     | 0wx24 => (PT_DOLLAR(getPP q),q1)
		     | 0wx26 => let val (c1,q2) = get q1
				in if c1=0wx26 then (PT_AND(getPos q,getPos q1),q2)
				   else (PT_AMPERSAND(getPP q),ungetChar(q2,c1))
				end
		     | 0wx27 => let val pos1 = getPos q
				    val (lit,pos2,q2) = getLit(pos1,c,q1)
				in (PT_LIT(lit,pos1,pos2),q2)
				end
		     | 0wx28 => (PT_LPAR(getPP q),q1)
		     | 0wx29 => (PT_RPAR(getPP q),q1)
		     | 0wx2A => let val (c1,q2) = get q1
				in if c1=0wx2A then (PT_REPP(getPos q,getPos q1),q2)
				   else (PT_REP(getPP q),ungetChar(q2,c1))
				end
		     | 0wx2B => let val (c1,q2) = get q1
				in if c1=0wx2B then (PT_PLUSS(getPos q,getPos q1),q2)
				   else (PT_PLUS(getPP q),ungetChar(q2,c1))
				end
		     | 0wx2C => (PT_COMMA(getPP q),q1)
		     | 0wx2D => let val (c1,q2) = get q1
				in if c1=0wx3E then (PT_TO(getPos q,getPos q1),q2)
				   else raise IllegalChar(ungetChar(q2,c1),getPos q,c)
				end
		     | 0wx2E => (PT_DOT(getPP q),q1)
		     | 0wx3B => (PT_SEMI(getPP q),q1)
		     | 0wx3C => let val (c1,q2) = get q1
				in if c1=0wx3F 
                                      then let val pos1 = getPos q
                                               val (pi,pos2,q3) = getPi(pos1,q2)
                                           in (PT_PI(pi,pos1,pos2),q3)
                                           end
                                   else (PT_STAGO(getPP q),ungetChar(q2,c1))
				end
		     | 0wx3D => (PT_EQ(getPP q),q1)
		     | 0wx3E => (PT_TAGC(getPP q),q1)
		     | 0wx3F => (PT_OPT(getPP q),q1)
                     | 0wx5C => let val (c1,q2) = get q1
				in if c1=0wxA then getToken q2
				   else raise IllegalChar(ungetChar(q2,c1),getPos q,c)
				end
		     | 0wx5E => (PT_HAT(getPP q),q1)
		     | 0wx5F => (PT_UNDER(getPP q),q1)
		     | 0wx7C => let val (c1,q2) = get q1
				in if c1=0wx7C then (PT_OR(getPos q,getPos q1),q2)
				   else (PT_ALT(getPP q),ungetChar(q2,c1))
				end
                                
		     | _     => if isNms c then let val (cs,pos2,q2) = getName (q,q1)
                                                    val name = c::cs
                                                    val tok =
                                                       if name=Targets then PT_TARGETS
                                                       else if name=Start then PT_START
                                                       else if name=Rules then PT_RULES
						       else if name=Prim then PT_PRIM
                                                       else (fn(p1,p2) => PT_NAME(name,p1,p2))
                                                in (tok(getPos q,pos2),q2)
						end
				else raise IllegalChar(q1,getPos q,c)
	       end

	    fun nextToken() = 
	       let val (tok,q1) = getToken(!q)
	       in tok before q := q1 
	       end
	    handle IllegalChar(q1,pos,c) => let val _ = errorBadChar pos c
                                                val _ = q := q1
                                            in nextToken()
                                            end
		 | Unclosed(q1,pos,what) => let val _ = errorUnclosed (getPos q1,pos) what
                                                val _ = q := q1
                                            in nextToken()
                                            end
	 in nextToken
	 end
   end
