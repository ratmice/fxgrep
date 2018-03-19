signature RegExp1 =
   sig
      datatype 'a RegExp = 
	 RE_NULL
       | RE_EMPTY
       | RE_UNDER
       | RE_BASIC of 'a
       | RE_DEEP of 'a
       | RE_OPT of 'a RegExp
       | RE_REP of 'a RegExp
       | RE_PLUS of 'a RegExp
       | RE_SEQ of 'a RegExp * 'a RegExp
       | RE_ALT of 'a RegExp * 'a RegExp

      val RegExp2String : ('a -> string) -> 'a RegExp -> string

      val makeAlt       : 'a RegExp list -> 'a RegExp
      val makeSeq       : 'a RegExp list -> 'a RegExp
      val compareRegExp : ('a * 'a -> order) -> 'a RegExp * 'a RegExp -> order
   end

structure RegExp1 : RegExp1 =
   struct
      open UtilList

      datatype 'a RegExp = 
	 RE_NULL
       | RE_EMPTY
       | RE_UNDER
       | RE_BASIC of 'a
       | RE_DEEP of 'a
       | RE_OPT of 'a RegExp
       | RE_REP of 'a RegExp
       | RE_PLUS of 'a RegExp
       | RE_SEQ of 'a RegExp * 'a RegExp
       | RE_ALT of 'a RegExp * 'a RegExp

      fun RegExp2String A2String re = 
         let fun doit prec re =
            case re
              of RE_NULL => "0"
	       | RE_EMPTY => ""
               | RE_UNDER => "_"
               | RE_BASIC a => (A2String a)^"/"
	       | RE_DEEP a => (A2String a)^"//"
               | RE_OPT re => doit 3 re^"?"
               | RE_REP re => doit 3 re^"*"
               | RE_PLUS re => doit 3 re^"+"
               | RE_SEQ(re1,re2) => let val (lpar,rpar) = if prec<=2 then ("","") else ("(",")")
                                    in lpar^doit 2 re1^","^doit 2 re2^rpar
                                    end
               | RE_ALT(re1,re2) => let val (lpar,rpar) = if prec<=1 then ("","") else ("(",")")
				    in lpar^doit 1 re1^"|"^doit 1 re2^rpar
				    end
         in doit 0 re
         end
      
      (*--------------------------------------------------------------------*)
      (* get the list of all descendants connected by SEQ/ALT.              *)
      (*--------------------------------------------------------------------*)
      fun getAltList nil = nil
	| getAltList (re::res) = 
	 case re
	   of RE_ALT(re1,re2) => getAltList(re1::re2::res)
	    | _ => re::getAltList res
      fun getSeqList nil = nil
	| getSeqList (re::res) = 
	 case re
	   of RE_SEQ(re1,re2) => getSeqList(re1::re2::res)
	    | _ => re::getSeqList res

      (*--------------------------------------------------------------------*)
      (* make a regexp connected by ALT/SEQ.                                *)
      (*--------------------------------------------------------------------*)
      fun makeAltSeq (con,null) res = 
	 let fun doit nil = null
	       | doit [re] = re
	       | doit (re1::res) = con(re1,doit res)
	 in doit res
	 end
      fun makeAlt res = makeAltSeq (RE_ALT,RE_NULL) res
      fun makeSeq res = makeAltSeq (RE_SEQ,RE_EMPTY) res

      (*--------------------------------------------------------------------*)
      (* compare two regular expressions.                                   *)
      (*--------------------------------------------------------------------*)
      fun compareRegExp compareA res = 
	 let fun doit res =
	    case res 
	      of (RE_NULL,RE_NULL) => EQUAL
	       | (RE_NULL,_) => LESS
	       | (_,RE_NULL) => GREATER
	       | (RE_EMPTY,RE_EMPTY) => EQUAL
	       | (RE_EMPTY,_) => LESS
	       | (_,RE_EMPTY) => GREATER
	       | (RE_UNDER,RE_UNDER) => EQUAL
	       | (RE_UNDER,_) => LESS
	       | (_,RE_UNDER) => GREATER
	       | (RE_BASIC a1,RE_BASIC a2) => compareA(a1,a2)
	       | (RE_BASIC _,_) => LESS
	       | (_,RE_BASIC _) => GREATER
	       | (RE_DEEP a1,RE_DEEP a2) => compareA(a1,a2)
	       | (RE_DEEP _,_) => LESS
	       | (_,RE_DEEP _) => GREATER
	       | (RE_OPT re1,RE_OPT re2) => doit (re1,re2)
	       | (RE_OPT _,_) => LESS
	       | (_,RE_OPT _) => GREATER
	       | (RE_REP re1,RE_REP re2) => doit (re1,re2)
	       | (RE_REP _,_) => LESS
	       | (_,RE_REP _) => GREATER
	       | (RE_PLUS re1,RE_PLUS re2) => doit (re1,re2)
	       | (RE_PLUS _,_) => LESS
	       | (_,RE_PLUS _) => GREATER
	       | (RE_SEQ res1,RE_SEQ res2) => doPair (res1,res2)
	       | (RE_SEQ _,_) => LESS
	       | (_,RE_SEQ _) => GREATER
	       | (RE_ALT res1,RE_ALT res2) => doPair (res1,res2)
	     and doPair ((x1,x2),(y1,y2)) =
		case doit (x1,y1) 
		  of EQUAL => doit (x2,y2)
		   | order => order
	 in doit res
	 end

      (*--------------------------------------------------------------------*)
      (* hash a regular expression to a word.                               *)
      (*--------------------------------------------------------------------*)
      (*fun hashRegExp hashA re =
	 let 
	    fun doit re =
	       case re
		 of RE_NULL => 0w0
		  | RE_EMPTY => 0w1
		  | RE_UNDER => 0w2
		  | RE_BASIC a => 0w3 + 0w6 * hashA a
		  | RE_OPT re1 => 0w4 + 0w6 * doit re1
		  | RE_REP re1 => 0w5 + 0w6 * doit re1
		  | RE_PLUS re1 => 0w6 + 0w6 * doit re1
		  | RE_SEQ res => 0w7 + 0w6 * doPair res
		  | RE_ALT res => 0w8 + 0w6 * doPair res
	    and doPair (re1,re2) = 
	       doit re1 + 0wx133 * doit re2 
	 in doit re
	 end*)

      (*--------------------------------------------------------------------*)
      (* normalize a regular expression, such that:                         *)
      (* - it does not contain RE_UNDER;                                    *)
      (* - RE_ALT groups are sorted;                                        *)
      (* - nested RE_ALT and RE_SEQ are flattened.                          *)
      (*--------------------------------------------------------------------*)
      (*fun normRegExp (normUnder,normBasic,compareBasic) re =
	 let fun norm re =
	    case re
	      of RE_NULL => RE_NULL
	       | RE_EMPTY => RE_EMPTY
	       | RE_UNDER => normUnder
	       | RE_BASIC a => normBasic a
	       | RE_OPT re1 => RE_OPT (norm re1)
	       | RE_REP re1 => RE_REP (norm re1)
	       | RE_PLUS re1 => RE_PLUS (norm re1)
	       | RE_SEQ(re1,re2) => let val res = getSeqList [re1,re2] 
					val lcs = map norm res
				    in makeSeq lcs
				    end
	       | RE_ALT(re1,re2) => let val res = getAltList [re1,re2] 
					val lcs = map norm res
					val lcs1 = sort (compareRegExp compareBasic) lcs
				    in makeAlt lcs1
				    end
	 in norm re
	 end*)

      (*fun regExpSymbols re = 
         let fun doit aas nil = aas
               | doit aas (re::res) = case re
                                        of RE_NULL => doit aas res
                                         | RE_EMPTY => doit aas res
                                         | RE_UNDER => doit aas res
                                         | RE_BASIC a => doit (a::aas) res
                                         | RE_OPT re1 => doit aas (re1::res)
                                         | RE_REP re1 => doit aas (re1::res)
                                         | RE_PLUS re1 => doit aas (re1::res)
                                         | RE_ALT(re1,re2) => doit aas (re1::re2::res)
                                         | RE_SEQ(re1,re2) => doit aas (re1::re2::res)
         in doit nil [re]
         end*)
   end      