functor TextPatLexer (structure Tokens : TextPat_TOKENS) : ARG_LEXER = 
   struct
      structure UserDeclarations = 
	 struct 
	    type pos = int
	    type svalue = Tokens.svalue
	    type ('a,'b) token = ('a,'b) Tokens.token 
	    type arg = UniChar.Vector
	 end

      open Tokens 

      (*---------------------------------------------------------------------*)
      (* ml-yacc requires the first argument of makeLexer to be a function   *)
      (* that reads characters. this argument is ignored since we deal with  *)
      (* vectors of XML characters given as second argument.                 *)
      (*---------------------------------------------------------------------*)
      fun makeLexer _ cv =
	 let 
	    val length = Vector.length cv
	       
	    val idx = ref 0
	       
	    fun get i = if i<length then (Vector.sub(cv,i),i+1) else (0wx0,i)
               

            fun decValue c = 
               let val w=c-0wx30 
               in if w<=0w9 then SOME w else NONE
               end

            fun hexValue c = 
               let val w=c-0wx30 
               in if w<=0w9 then SOME w 
                  else let val w=c-0wx41
                       in if w<=0w5 then SOME(w+0w10) 
                          else let val w=c-0wx61
                               in if w<=0w5 then SOME(w+0w10) 
                                  else NONE
                               end
                       end
               end

	    fun do_num w i = 
	       let val (c,i1) = get i
	       in case decValue c 
                    of NONE => if c=0wx20 then (w,i1) else (w,i)
                     | SOME w1 => do_num (0w10*w+w1) i1
	       end

	    fun do_hex w i = 
	       let val (c,i1) = get i
	       in case hexValue c 
                    of NONE => if c=0wx20 then (w,i1) else (w,i)
                     | SOME w1 => do_hex (0w16*w+w1) i1
	       end

	    fun getToken i =
	       let val (c,i1) = get i
	       in case c
		    of 0wx00 => (PT_EOT(i,i),i1)
		     | 0wx20 => (PT_BLANK(i1,i1),i1)
		     | 0wx24 => (PT_DOLLAR(i1,i1),i1)
		     | 0wx28 => (PT_LPAR(i1,i1),i1)
		     | 0wx29 => (PT_RPAR(i1,i1),i1)
		     | 0wx2A => (PT_REP(i1,i1),i1)
		     | 0wx2B => (PT_PLUS(i1,i1),i1)
		     | 0wx2D => (PT_MINUS(i1,i1),i1)
		     | 0wx2E => (PT_DOT(i1,i1),i1)
		     | 0wx3F => (PT_OPT(i1,i1),i1)
		     | 0wx5B => (PT_LBRACK(i1,i1),i1)
		     | 0wx5C => let val (c1,i2) = get i1
				in case c1
				     of 0wx00 => (PT_CHAR(c,i1,i1),i1)
				      | 0wx6E => (PT_CHAR(0wxA,i1,i2),i2)
				      | 0wx72 => (PT_CHAR(0wxD,i1,i2),i2)
				      | 0wx74 => (PT_CHAR(0wx9,i1,i2),i2)
				      | 0wx78 => let val (c2,i3) = get i2
                                                 in case hexValue c2
                                                      of NONE => (PT_CHAR(c1,i1,i2),i2)
                                                       | SOME w => let val (n,i4) = do_hex w i3
                                                                   in (PT_CHAR(n,i1,i4),i4)
                                                                   end
                                                 end
				      | _     => case decValue c1 
                                                   of NONE => (PT_CHAR(c1,i1,i2),i2)
                                                    | SOME w => let val (n,i3) = do_num w i2
                                                                in (PT_CHAR(n,i1,i3),i3)
                                                                end
				end
		     | 0wx5D => (PT_RBRACK(i1,i1),i1)
		     | 0wx5E => (PT_HAT(i1,i1),i1)
		     | 0wx7C => (PT_ALT(i1,i1),i1)
		     | 0wx7E => (PT_TILDE(i1,i1),i1)
		     | _     => (PT_CHAR(c,i1,i1),i1)
	       end
	    
	    fun nextToken() = 
	       let 
		  val (tok,i1) = getToken (!idx)
		  val _ = idx := i1
	       in tok
	       end
	 in 
	    nextToken
	 end
   end
