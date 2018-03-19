functor PatternLexer
  (structure Tokens : Pattern_TOKENS
   type State
   val get : State -> UniChar.Char * State
   val getPos : State -> Errors.Position
   val getPP : State -> Errors.Position * Errors.Position
   val errorUnclosed : Errors.Position * Errors.Position -> string -> unit
   val errorBadChar : Errors.Position -> UniChar.Char -> unit) =
     struct
       open Errors Tokens UniChar UniClasses
       
       fun makeLexer q = 
	 let 
	   exception IllegalChar of State * Position * Char
	   exception Unclosed of State * Position * string
	    
	   fun getName (last,q) = 
	     let val (c,q1) = get q
	     in if isName c 
		  then let val (cs,pos2,q2) = getName(q,q1)
		       in (c::cs,pos2,q2)
		       end
		else (nil,getPos last,q)
	     end

	   fun decValue c = 
	     let val w=c-0wx30 
	     in if w<=0w9 then SOME(Chars.toInt w) else NONE
	     end
            
	   fun getNumber (n,last,q) = 
	     let val (c,q1) = get q
	     in case decValue c 
	       of NONE => (n,getPos last,q)
	     | SOME i => getNumber(10*n+i,q,q1)
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
	     | 0wx23 => (PT_HASH(getPP q),q1)
	     | 0wx24 => (PT_DOLLAR(getPP q),q1)
	     | 0wx25 => (PT_PERCENT(getPP q),q1)
	     | 0wx26 => 
			let 
			  val (c1,q2) = get q1
			in 
			  if c1=0wx26 then (PT_AND(getPos q,getPos q1),q2)
			  else (PT_AMPERSAND (getPP q),q1)
			end
	     | 0wx27 => let val pos1 = getPos q
			    val (lit,pos2,q2) = getLit(pos1,c,q1)
			in (PT_LIT(lit,pos1,pos2),q2)
			end
	     | 0wx28 => (PT_LPAR(getPP q),q1)
	     | 0wx29 => (PT_RPAR(getPP q),q1)
	     | 0wx2A => let val (c1,q2) = get q1
			in if c1=0wx2A then (PT_REPP(getPos q,getPos q1),q2)
			   else (PT_STAR(getPP q),q1)
			end
	     | 0wx2B => let val (c1,q2) = get q1
			in if c1=0wx2B then (PT_PLUSS(getPos q,getPos q1),q2)
			   else (PT_PLUS(getPP q),q1)
			end
	     | 0wx2C => (PT_COMMA(getPP q),q1)
	     | 0wx2D => (PT_MINUS(getPP q),q1)
	     | 0wx2E => (PT_DOT(getPP q),q1)
	     | 0wx2F => let val (c1,q2) = get q1
			in if c1=0wx2F then (PT_DOUBLE(getPos q,getPos q1),q2)
			   else (PT_SOLID(getPP q),q1)
			end
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
	     | 0wx40 => (PT_AT(getPP q),q1)
	     | 0wx5B => (PT_LBRACK(getPP q),q1)
	     | 0wx5D => (PT_RBRACK(getPP q),q1)
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
			else case decValue c 
			  of SOME i => let val (n,pos2,q2) = getNumber(i,q,q1)
				       in (PT_NUM(n,getPos q,pos2),q2)
				       end
			| _ => raise IllegalChar(q1,getPos q,c)
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
   