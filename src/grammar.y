(*---------------------------------------------------------------------------*)
(* ml-yacc specification file for tree patterns, one-level contexts and the  *)
(* pattern. A dummy token at the beginning of the token stream indicates     *)
(* which of the three start symbols must be used. Thus, only one of the 3    *)
(* components of the result is significant.                                  *)
(*---------------------------------------------------------------------------*)
open DocDtd GramData GrepError GramTables GramUtil TextPatParser UniChar

fun checkName (pos,name,exp) = 
   if name=exp then () else errorBadName pos (name,exp)

%%

%verbose

%arg (dtd,tab) : Dtd * XTable
%name Grammar
(* %verbose *)

%eop PT_EOT
%pos Errors.Position

%term    PT_EOT
       | PT_ALT
       | PT_AMPERSAND
       | PT_AND
       | PT_COMMA
       | PT_DOLLAR
       | PT_DOT
       | PT_EQ
       | PT_HAT
       | PT_LIT of UniChar.Vector
       | PT_LPAR
       | PT_NAME of UniChar.Data
       | PT_NL
       | PT_NOT
       | PT_OPT
       | PT_OR
       | PT_PI of Errors.Position * UniChar.Vector
       | PT_PLUS
       | PT_PLUSS
       | PT_PRIM
       | PT_REP
       | PT_REPP
       | PT_RPAR
       | PT_RULES 
       | PT_SEMI
       | PT_STAGO
       | PT_START
       | PT_TAGC
       | PT_TARGETS
       | PT_TILDE
       | PT_TO
       | PT_UNDER
       | PTX_RULE
       | PTX_FEXP
       | PTX_TARGET
       | PTX_FORM
       | PTX_GRAMMAR

%nonterm START of YResult
       | GRAM of Grammar * MatchSpec
       | RULES of unit
       | RULS of unit
       | RUL of unit
       | TRGTS of int list
       | TRGTS2 of Secondaries
       | TARGS of int list
       | TARGS_LIST of int list list
       | STRTS of ForestExp list
       | SEXP of ForestExp
       | SEXPS of ForestExp list
       | SLIT of Sign * XRegExp
       | SRE of XRegExp
       | FEXP of ForestExp
       | FLIT of Sign * XRegExp
       | XRE of XRegExp
       | XRE_A of XRegExp
       | XRE_B of XRegExp
       | XRE_C of XRegExp
       | X of int
       | RHS of Rhs
       | STAG of TagPattern
       | GIPAT of GiPattern
       | GIS of int list
       | GI of int
       | APS of AttPattern list
       | AP of AttPat
       | NL
       | NLO
       | NLOR
       | SEM
       | NAME of Data
       | NAMX of Data

       | FORM of int Formula.Formula
       | AND_FORM of int Formula.Formula
       | OR_FORM of int Formula.Formula
       | NOT_FORM of int Formula.Formula
       | PRIM of int Formula.Formula
 
%start START
%noshift PT_EOT 
%keyword PTX_RULE PTX_FEXP PTX_TARGET PTX_FORM

%%

START: PTX_RULE RHS                   (Y_RULE RHS)
     | PTX_FEXP FEXP                  (Y_FEXP FEXP)
     | PTX_TARGET TARGS               (Y_TARGET TARGS)
     | PTX_FORM FORM                  (Y_FORM FORM)
     | PTX_GRAMMAR GRAM               (Y_GRAMMAR GRAM)
			              
RHS  : STAG FEXP                      (RHS_TREE(STAG,FEXP))
     | PT_LIT                         (RHS_TEXT(parseTextPattern false (PT_LITleft,PT_LIT)))
     | PT_PI FEXP                     (RHS_PI(parseTextPattern false PT_PI,FEXP))

STAG : PT_STAGO GIPAT APS PT_TAGC     (GIPAT,APS)
			              
GIPAT: PT_REP                         (GI_DOT)
     | GIS                            (GI_POS (sortInt GIS))
     | PT_NOT GIS                     (GI_NEG (sortInt GIS))
			              
GI   : NAME                           (Element2Doc dtd NAME)

GIS  : GI                             ([GI])
GIS  : GI PT_ALT GIS                  (GI::GIS)

APS  :                                (nil)
     | AP APS                         ((true,AP)::APS)
     | PT_NOT AP APS                  ((false,AP)::APS)
			              
AP   : NAME                           (AT_NAME(Element2Doc dtd NAME))
     | NAME PT_EQ PT_LIT              (AT_VALUE(Element2Doc dtd NAME,
                                                parseTextPattern true (PT_LITleft,PT_LIT)))
     | NAME PT_TILDE PT_LIT           (AT_VALUE(Element2Doc dtd NAME,
                                                parseTextPattern false (PT_LITleft,PT_LIT)))

FEXP : FLIT                           ([FLIT])
     | FLIT PT_AND FEXP               (FLIT::FEXP)

FLIT : XRE                            (true,XRE)
     | PT_NOT XRE                     (false,XRE)
				      
XRE  :                                (XRE_WHITE)
     | SRE                            (SRE)

XRE_C: XRE_B                          (XRE_B)
     | XRE_C PT_ALT XRE_B             (RE_ALT(XRE_C,XRE_B))
			              
XRE_B: XRE_A                          (XRE_A)
     | XRE_B XRE_A                    (if XRE_B=XRE_UNDER orelse XRE_A=XRE_UNDER 
                                          then RE_SEQ(XRE_B,XRE_A)
                                       else makeSeq [XRE_B,XRE_WHITE,XRE_A])
     | XRE_B PT_COMMA XRE_A           (RE_SEQ(XRE_B,XRE_A))
			              
XRE_A: PT_DOT                         (RE_BASIC xTrue)
     | PT_TILDE                       (XRE_WHITE)
     | X                              (RE_BASIC X)
     | PT_LPAR XRE_C PT_RPAR          (XRE_C)
     | XRE_A PT_PLUS                  (if XRE_A=XRE_UNDER then RE_PLUS XRE_A
                                       else RE_PLUS(RE_SEQ(XRE_A,XRE_WHITE)))
     | XRE_A PT_PLUSS                 (RE_PLUS XRE_A)
     | XRE_A PT_REP                   (if XRE_A=XRE_UNDER then RE_REP XRE_A
                                       else RE_REP(RE_SEQ(XRE_A,XRE_WHITE)))
     | XRE_A PT_REPP                  (RE_REP XRE_A)
     | XRE_A PT_OPT                   (RE_OPT XRE_A)
     | PT_UNDER                       (XRE_UNDER)
 

GRAM : PRIM STRTS RULES         (let 
					 val (max,rules) = extractXTable tab
                                       in ((max,STRTS,rules),((PRIM,nil),nil):MatchSpec)
                                       end)
     | PRIM TRGTS STRTS RULES         (let 
					 val (max,rules) = extractXTable tab
                                       in ((max,STRTS,rules),((PRIM,TRGTS),nil))
                                       end)
     | PRIM TRGTS TRGTS2 STRTS RULES  (let val (max,rules) = extractXTable tab
				       in ((max,STRTS,rules),((PRIM,TRGTS),TRGTS2))
                                       end)
NL   : PT_NL                          ()
     | PT_NL NL                       ()
NLO  :                                ()
     | NL                             ()
SEM  : NL                             ()
     | NLO PT_SEMI NLO                ()
NLOR : NL                             ()
     | NLO PT_OR NLO                  ()

NAMX : PT_NAME                        (PT_NAME)
X    : NAMX                           (useX tab (NAMXleft,NAMX))


FORM : FORM PT_ALT AND_FORM (Formula.OR (FORM,AND_FORM))
     | AND_FORM            (AND_FORM)

AND_FORM : 
       AND_FORM PT_AMPERSAND NOT_FORM (Formula.AND (AND_FORM, NOT_FORM))
     | NOT_FORM                 (NOT_FORM)

NOT_FORM :
       PT_LPAR FORM PT_RPAR     (FORM)
     | PT_NOT NOT_FORM          (Formula.NOT NOT_FORM)
     | X                        (Formula.VAR X)

PRIM: PT_PRIM NLO FORM SEM      (FORM)


TARGS: X                              ([X])
     | X TARGS                        (X::TARGS)
    
TRGTS: PT_TARGETS NLO TARGS SEM       (ListMergeSort.sort Int.> TARGS)

TRGTS2: PRIM PT_TARGETS NLO TARGS SEM     ([(PRIM,ListMergeSort.sort Int.> TARGS)])
      | PRIM PT_TARGETS NLO TARGS SEM TRGTS2  
                                     ((PRIM,ListMergeSort.sort Int.> TARGS)::TRGTS2)

STRTS: PT_START NLO SEXPS             (SEXPS)
RULES: NLO RULS                       ()
     | NLO                            ()

RULS : RUL NLO                        ()
RULS : RUL SEM RULS                   ()
RUL  : NAME PT_TO RHS                 (defineX tab (declareX tab (Data2Vector NAME),RHS))

SEXPS: SEXP NLOR PT_RULES             ([SEXP])
     | SEXP NLOR SEXPS                (SEXP::SEXPS)

SEXP : SLIT                           ([SLIT])
     | SLIT PT_AND SEXP               (SLIT::SEXP)

SLIT : SRE                            (true,SRE)
     | PT_NOT SRE                     (false,SRE)
				      
SRE  : XRE_C                          (if XRE_C=XRE_UNDER then XRE_C
                                       else makeSeq [XRE_WHITE,XRE_C,XRE_WHITE])
     | PT_HAT XRE_C                   (if XRE_C=XRE_UNDER then XRE_C
                                       else RE_SEQ(XRE_C,XRE_WHITE))
     | PT_DOLLAR                      (RE_EMPTY)
     | PT_HAT PT_DOLLAR               (RE_EMPTY)
     | XRE_C PT_DOLLAR                (if XRE_C=XRE_UNDER then XRE_C
                                       else RE_SEQ(XRE_WHITE,XRE_C))
     | PT_HAT XRE_C PT_DOLLAR         (XRE_C)


NAME : NAMX                           (NAMX)
     | PT_RULES                       (Rules)
