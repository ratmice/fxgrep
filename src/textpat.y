(*---------------------------------------------------------------------------*)
(* ml-yacc specification file for the following grammar:                     *)
(*                                                                           *)
(*   TEXTPAT ::= TP?                                                         *)
(*        TP ::= CHARPAT                                                     *)
(*           |   '(' TP ')'                                                  *)
(*           |   TP '?'                                                      *)
(*           |   TP '*'                                                      *)
(*           |   TP '+'                                                      *)
(*           |   TP TP                                                       *)
(*           |   TP '|' TP                                                   *)
(*   CHARPAT ::= '^' | '$' | '.'                                             *)
(*           |   CHAR                                                        *)
(*           |   '[' '^'? (RANGE|CHAR)+ ']'                                  *)
(*     RANGE ::= CHAR '-' CHAR                                               *)
(*                                                                           *)
(* Many extra rules are necessary for avoiding shift/reduce/reduce conflicts.*)
(*---------------------------------------------------------------------------*)
open CharRanges GramData GramUtil

val altChar    = 0wx7C : UniChar.Char
val blankChar  = 0wx20 : UniChar.Char
val dollarChar = 0wx24 : UniChar.Char
val dotChar    = 0wx2E : UniChar.Char
val hatChar    = 0wx5E : UniChar.Char
val lbrackChar = 0wx5B : UniChar.Char
val lparChar   = 0wx28 : UniChar.Char
val minusChar  = 0wx2D : UniChar.Char
val optChar    = 0wx7C : UniChar.Char
val plusChar   = 0wx2B : UniChar.Char
val rbrackChar = 0wx5D : UniChar.Char
val repChar    = 0wx2A : UniChar.Char
val rparChar   = 0wx29 : UniChar.Char
val tildeChar  = 0wx7E : UniChar.Char

val hatRange    = singleCharRange hatChar
val minusRange  = singleCharRange minusChar
val rbrackRange = singleCharRange rbrackChar
val wsRange     = Data2CharRange [0wx09,0wx0A,0wx0D,0wx20]

%%

%name TextPat
(* %verbose *)

%eop PT_EOT
%pos int

%term    PT_EOT
       | PT_ALT
       | PT_BLANK
       | PT_CHAR of UniChar.Char
       | PT_DOLLAR
       | PT_DOT
       | PT_HAT
       | PT_LBRACK
       | PT_LPAR
       | PT_MINUS
       | PT_OPT
       | PT_PLUS
       | PT_RBRACK
       | PT_REP
       | PT_RPAR
       | PT_TILDE

%nonterm TXTPAT of TextPattern option
       | TXT_A of TextPattern
       | TXT_B of TextPattern
       | TXT_C of TextPattern
       | CHARPAT of CharPattern
       | RANGE of CharRanges.CharRange
       | RANGE_A of CharRanges.CharRange
       | CHAR of UniChar.Char
       | CHAR_A of UniChar.Char

%start TXTPAT
%noshift PT_EOT 

%%

TXTPAT:  TXT_C                    (SOME TXT_C)
     |                            (NONE)
                                  
TXT_C:   TXT_B                    (TXT_B)
     |   TXT_C PT_ALT TXT_B       (RE_ALT(TXT_C,TXT_B))
                                  
TXT_B:   TXT_A                    (TXT_A)
     |   TXT_B TXT_A              (RE_SEQ(TXT_B,TXT_A))
                                  
TXT_A :  CHARPAT                  (RE_BASIC CHARPAT)
     |   PT_BLANK                 (RE_PLUS(RE_BASIC CP_WHITE))
     |   PT_LPAR TXT_C PT_RPAR    (TXT_C)
     |   TXT_A PT_PLUS            (RE_PLUS TXT_A)
     |   TXT_A PT_REP             (RE_REP TXT_A)
     |   TXT_A PT_OPT             (RE_OPT TXT_A)
                                      
CHARPAT: PT_HAT                   (CP_START)
     |   PT_DOLLAR                (CP_END)
     |   PT_CHAR                  (CP_POS(singleCharRange PT_CHAR))
     |   PT_DOT                   (CP_NEG emptyCharRange)
     |   PT_MINUS                 (CP_POS minusRange)
     |   PT_TILDE                 (CP_WHITE)
     |   PT_RBRACK                (CP_POS rbrackRange)
     |   PT_LBRACK RANGE_A        (CP_POS(normCharRange RANGE_A))
     |   PT_LBRACK PT_MINUS RANGE (CP_POS(normCharRange(mergeCharRanges(minusRange,RANGE))))
     |   PT_LBRACK PT_MINUS PT_RBRACK 
                                  (CP_POS minusRange)
     |   PT_LBRACK PT_HAT RANGE   (CP_NEG(normCharRange RANGE))
     |   PT_LBRACK PT_HAT PT_RBRACK 
                                  (CP_POS hatRange)
     |   PT_LBRACK PT_HAT PT_MINUS RANGE 
                                  (CP_NEG(normCharRange(mergeCharRanges(minusRange,RANGE))))
     |   PT_LBRACK PT_HAT PT_MINUS PT_RBRACK 
                                  (CP_NEG minusRange)


RANGE:   CHAR PT_RBRACK           (singleCharRange CHAR)
     |   CHAR PT_MINUS PT_RBRACK  (mergeCharRanges(singleCharRange CHAR,minusRange))
     |   CHAR PT_MINUS CHAR PT_RBRACK 
                                  (intervalCharRange(CHAR1,CHAR2))
     |   CHAR PT_MINUS CHAR PT_MINUS PT_RBRACK 
                                  (mergeCharRanges(intervalCharRange(CHAR1,CHAR2),minusRange))
     |   CHAR RANGE               (mergeCharRanges(singleCharRange CHAR,RANGE))
     |   CHAR PT_MINUS CHAR RANGE (mergeCharRanges(intervalCharRange(CHAR1,CHAR2),RANGE))
     |   PT_TILDE CHAR RANGE      (mergeCharRanges(wsRange,RANGE))

RANGE_A: CHAR_A PT_RBRACK         (singleCharRange CHAR_A)
     |   CHAR_A PT_MINUS PT_RBRACK  
                                  (mergeCharRanges(singleCharRange CHAR_A,minusRange))
     |   CHAR_A PT_MINUS CHAR PT_RBRACK 
                                  (intervalCharRange(CHAR_A,CHAR))
     |   CHAR_A PT_MINUS CHAR PT_MINUS PT_RBRACK 
                                  (mergeCharRanges(intervalCharRange(CHAR_A,CHAR),minusRange))
     |   CHAR_A RANGE             (mergeCharRanges(singleCharRange CHAR_A,RANGE))
     |   CHAR_A PT_MINUS CHAR RANGE 
                                  (mergeCharRanges(intervalCharRange(CHAR_A,CHAR),RANGE))
     |   PT_TILDE CHAR RANGE      (mergeCharRanges(wsRange,RANGE))

CHAR:    PT_HAT                   (hatChar)
     |   CHAR_A                   (CHAR_A)
                                  
CHAR_A:  PT_ALT                   (altChar)
     |   PT_BLANK                 (blankChar)
     |   PT_DOLLAR                (dollarChar)
     |   PT_DOT                   (dotChar)
     |   PT_LBRACK                (lbrackChar)
     |   PT_LPAR                  (lparChar)
     |   PT_OPT                   (optChar)
     |   PT_PLUS                  (plusChar)
     |   PT_REP                   (repChar)
     |   PT_RPAR                  (rparChar)
     |   PT_CHAR                  (PT_CHAR)
