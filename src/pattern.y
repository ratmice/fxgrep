(*---------------------------------------------------------------------------*)
(* ml-yacc specification file for tree patterns, one-level contexts and the  *)
(* pattern. A dummy token at the beginning of the token stream indicates     *)
(* which of the three start symbols must be used. Thus, only one of the 3    *)
(* components of the result is sinificant.                                   *)
(*---------------------------------------------------------------------------*)
open DocDtd GramData GramUtil TextPatParser ToDefaultForestPattern

%%

%arg (dtd) : Dtd
%name Pattern
%verbose

%eop PT_EOT
%pos Errors.Position

%term    PT_EOT
       | PT_ALT
       | PT_AT
       | PT_AND
       | PT_AMPERSAND
       | PT_COMMA
       | PT_DOLLAR
       | PT_DOUBLE
       | PT_DOT
       | PT_EQ
       | PT_HASH
       | PT_HAT
       | PT_LIT of UniChar.Vector
       | PT_LBRACK
       | PT_LPAR
       | PT_MINUS
       | PT_NAME of UniChar.Data
       | PT_NOT
       | PT_NUM of int
       | PT_OPT
       | PT_OR
       | PT_PERCENT
       | PT_PI of Errors.Position * UniChar.Vector
       | PT_PLUS
       | PT_PLUSS
       | PT_RBRACK 
       | PT_REPP
       | PT_RPAR
       | PT_SOLID
       | PT_STAGO
       | PT_STAR
       | PT_TAGC
       | PT_TILDE
       | PT_UNDER

%nonterm START of Pattern
       | FP of ForestPattern
       | FP' of ForestPattern
       | FP_A of ForestPattern
       | FP_B of ForestPattern
       | FP_C of ToDefaultForestPattern
       | FP_D of ToDefaultForestPattern
       | FP_T of ForestPattern
       | NP of TargetNodePattern
       | NP_A of NodePattern
       | GP of GiPattern
       | GIS of int list
       | GI of int
       | SQS of (bool * Qualifier) list
       | QS of (bool * Qualifier) list
       | QS' of (bool * Qualifier) list
       | Q of Qualifier
       | AP of AttPat
       | SIGN of bool
       | IP_A of IncompletePath
       | IP_B of IncompletePath
       | IP_C of IncompletePath
       | IP_D of bool * IncompletePath
       | IP_E of (bool * (bool * IncompletePath))
       | IP_F of (bool * (bool * IncompletePath)) list
       | CP_A of CompletePath
       | CP_B of (bool * IncompletePath) * TargetNodePattern
       | CP_C of TopLevelTreePattern
       | PAT_A of TopLevelTreePattern
       | PAT of (bool * ForestPattern) list * (bool * TopLevelTreePattern)
       | PATS of Pattern
       | PQ of (bool * ForestPattern)
       | PQS of (bool * ForestPattern) list

%start START
%noshift PT_EOT 

%left PT_EOT
%right PT_STAR

%%

NP_A : PT_DOT QS                       (PT_DOTleft,NT_TRUE,QS)
     | GP QS                           (GPleft,NT_GI GP,QS)
     | PT_LIT                          (PT_LITleft,NT_TEXT(parseTextPattern false
                                                (PT_LITleft,PT_LIT)),nil)
     | PT_PI SQS                       (PT_PIleft,NT_PI(parseTextPattern false PT_PI),SQS)

NP   : NP_A                               (false,NP_A)
     | PT_PERCENT PT_LPAR NP_A PT_RPAR  (true,NP_A) (*true means it is a secondary target*)
     | PT_PERCENT NP_A                  (true,NP_A)

GP   : GI                              (GI_POS [GI])
     | PT_STAGO PT_LIT PT_TAGC         (GI_REG (parseTextPattern true (PT_LITleft,PT_LIT)))
     | PT_STAR                         (GI_DOT)
     | PT_STAGO SIGN GIS               (if SIGN then GI_POS (sortInt GIS)
                                        else GI_NEG (sortInt (GIS@auxGis))) 

GI   : PT_NAME                         (Element2Doc dtd PT_NAME)
GIS  : GI PT_TAGC                      ([GI]) 
     | GI PT_ALT GIS                   (GI::GIS)

SIGN :                                 (true)
     | PT_NOT                          (false)

SQS  :                                 (nil)
     | PT_LBRACK SIGN FP PT_RBRACK SQS ((SIGN,Q_CHILDREN FP)::SQS)

QS   :                                 (nil)
     | PT_LBRACK Q PT_RBRACK QS        ((true,Q)::QS)
     | PT_LBRACK PT_NOT Q PT_RBRACK QS ((false,Q)::QS)
Q    : PT_AT AP                        (Q_ATT AP)
     | FP                              (Q_CHILDREN FP)

AP   : PT_NAME                         (AT_NAME (Element2Doc dtd PT_NAME))
     | PT_NAME PT_EQ PT_LIT            (AT_VALUE(Element2Doc dtd PT_NAME,
                                                 parseTextPattern true (PT_LITleft,PT_LIT)))
     | PT_NAME PT_TILDE PT_LIT         (AT_VALUE(Element2Doc dtd PT_NAME,
                                                 parseTextPattern false (PT_LITleft,PT_LIT)))

FP   :                                 (FP_UNDER defaultPos)
     | FP_D                            (let
					  val fp = undefaultedForestPattern FP_D 
					in
					  if isFP_UNDER fp then fp
					  else makeSeq [FP_UNDER FP_Dleft,fp,FP_UNDER FP_Dright]
					end)
     | PT_HAT FP_D                     (let
					  val fp = undefaultedForestPattern FP_D 
					in
					  if isFP_UNDER fp then fp
					  else 
					    case FP_D of
					      EXACT fp => makeSeq [fp,FP_UNDER FP_Dright]
					    | TRAILING fp => makeSeq [fp,FP_UNDER FP_Dright]
					    | _ => makeSeq [FP_WHITE FP_Dleft,fp,FP_UNDER FP_Dright]
					end)

     | FP_D PT_DOLLAR                  (let
					  val fp = undefaultedForestPattern FP_D 
					in
					  if isFP_UNDER fp then fp
					  else 
					    case FP_D of
					      EXACT fp => makeSeq [FP_UNDER FP_Dleft,fp]
					    | LEADING fp => makeSeq [FP_UNDER FP_Dleft,fp]
					    | _ => makeSeq [FP_UNDER FP_Dleft,fp,FP_WHITE FP_Dright]
					end)
     | PT_HAT FP_D PT_DOLLAR           (let
					  val fp = undefaultedForestPattern FP_D 
					in
					  if isFP_UNDER fp then fp
					  else 
					    case FP_D of
					      EXACT fp => fp
					    | LEADING fp => makeSeq [FP_WHITE FP_Dleft,fp]
					    | TRAILING fp => makeSeq [fp,FP_WHITE FP_Dright]
					    | BOTH fp => makeSeq [FP_WHITE FP_Dleft,fp,FP_WHITE FP_Dright]
					end)

     | PT_DOLLAR                       (RE_EMPTY)
     | PT_HAT                          (RE_EMPTY)


FP_D : FP_C                            (FP_C)
     | FP_D PT_ALT FP_C                (EXACT (RE_ALT(undefaultedForestPattern FP_D,defaultedForestPattern FP_C)))

(* a sequence of forest patterns possibly preceded, separated or
 followed by commas; a comma prohibits the presence of white spaces *)
FP_C : FP_B                            (if isFP_UNDER FP_B orelse isFP_WHITE FP_B then EXACT FP_B
					else BOTH FP_B)
     | PT_COMMA                        (EXACT RE_EMPTY)
     | PT_COMMA FP_B                   (if isFP_UNDER FP_B orelse isFP_WHITE FP_B then EXACT FP_B
					else TRAILING FP_B)
     | FP_B PT_COMMA                   (if isFP_UNDER FP_B orelse isFP_WHITE FP_B then EXACT FP_B
					else LEADING FP_B)
     | PT_COMMA FP_B PT_COMMA          (EXACT FP_B)
			              
FP_B : FP_A               %prec PT_EOT (FP_A)
     | FP_B FP_A          %prec PT_EOT (if isFP_UNDER FP_B orelse isFP_UNDER FP_A
                                           then RE_SEQ(FP_B,FP_A)
                                        else makeSeq [FP_B,FP_WHITE FP_Bright,FP_A])
     | FP_B PT_COMMA FP_A %prec PT_EOT (RE_SEQ(FP_B,FP_A))
			              
FP_A : FP_A PT_PLUS                    (if isFP_UNDER FP_A then RE_PLUS FP_A
                                        else RE_PLUS(RE_SEQ(FP_A,FP_WHITE FP_Aright)))
     | FP_A PT_PLUSS                   (RE_PLUS FP_A)
     | FP_A PT_STAR                    (if isFP_UNDER FP_A then RE_REP FP_A
                                        else RE_REP(RE_SEQ(FP_A,FP_WHITE FP_Aright)))
     | FP_A PT_REPP                    (RE_REP FP_A)
     | FP_A PT_OPT                     (RE_OPT FP_A)
     | PT_UNDER                        (FP_UNDER PT_UNDERleft)
     | PT_TILDE                        (FP_WHITE PT_TILDEleft)
     | FP_T                            (FP_T)


FP_T : PT_LPAR CP_A PT_RPAR            (RE_BASIC (TP (true,CP_A)))
     | PT_LPAR PT_DOUBLE NP PT_RPAR    (RE_BASIC (TP (false,CP_NODE(NP))))
     | PT_LPAR PT_DOUBLE CP_A PT_RPAR  (RE_BASIC (TP (false,CP_A)))
     | NP                              (RE_BASIC (TP (true,CP_NODE(NP))))
     | PT_LPAR NP PT_RPAR              (RE_BASIC (TP (true,CP_NODE(NP))))
     | PT_LPAR FP' PT_RPAR             (FP')
     | PT_HASH                         (RE_BASIC (HASH))
 
FP'  : PT_LPAR FP' PT_RPAR             (FP')
     | FP_D PT_ALT FP_B                (RE_ALT(defaultedForestPattern FP_D,FP_B))
     | FP_B FP_A                       (if isFP_UNDER FP_B orelse isFP_UNDER FP_A
					  then RE_SEQ(FP_B,FP_A)
                                        else makeSeq [FP_B,FP_WHITE FP_Bright,FP_A])
     | FP_B PT_COMMA FP_A              (RE_SEQ(FP_B,FP_A))
     | FP_A PT_PLUS                    (if isFP_UNDER FP_A then RE_PLUS FP_A
                                        else RE_PLUS(RE_SEQ(FP_A,FP_WHITE FP_Aright)))
     | FP_A PT_PLUSS                   (RE_PLUS FP_A)
     | FP_A PT_STAR                    (if isFP_UNDER FP_A then RE_REP FP_A
                                        else RE_REP(RE_SEQ(FP_A,FP_WHITE FP_Aright)))
     | FP_A PT_REPP                    (RE_REP FP_A)
     | FP_A PT_OPT                     (RE_OPT FP_A)
     | PT_TILDE                        (FP_WHITE PT_TILDEleft) 
     | PT_UNDER                        (FP_UNDER PT_UNDERleft) 

IP_A : IP_B                            (IP_B)
     | IP_B PT_OR IP_A                 (RegExp1.RE_ALT(IP_B,IP_A))

IP_B : IP_C                            (IP_C)
     | IP_B IP_C                       (RegExp1.RE_SEQ(IP_B,IP_C))

IP_C : IP_C PT_PLUS                    (RegExp1.RE_PLUS(IP_C))
     | IP_C PT_OPT                     (RegExp1.RE_OPT(IP_C))
     | NP PT_SOLID                     (RegExp1.RE_BASIC(NP))
     | NP PT_DOUBLE                    (RegExp1.RE_DEEP(NP))
     | PT_LPAR IP_A PT_RPAR            (IP_A)

CP_A : IP_B NP                         (CP_COMPOSED(IP_B,NP))
     | IP_B NP PT_OR CP_A              (CP_OR(CP_COMPOSED(IP_B,NP),CP_A))

(* incomplete path possibly preceded by / or // *)
IP_D : IP_B                            (true,IP_B)
     | PT_SOLID IP_B                   (true,IP_B)
     | PT_LPAR PT_SOLID IP_B PT_RPAR   (true,IP_B)
     | PT_DOUBLE IP_B                  (false,IP_B)
     | PT_LPAR PT_DOUBLE IP_B PT_RPAR  (false,IP_B)

(* incomplete path possibly preceded by / or //, possibly preceded by ! *)
IP_E : IP_D                            (true,IP_D)
     | PT_NOT IP_D                     (false,IP_D)
     | PT_LPAR PT_NOT IP_D PT_RPAR     (false,IP_D)

(* conjunction of incomplete paths *)
IP_F : IP_E                             ([IP_E])
     | IP_E PT_AMPERSAND IP_F           (IP_E::IP_F)

(* complete path having just one incomplete path possibly preceded by / or //*)
(*CP_B : IP_D NP (IP_D,NP) would lead to shift reduce conflicts*)
CP_B : IP_B NP                           ((true,IP_B),NP)
     | PT_SOLID IP_B NP                  ((true,IP_B),NP)
     | PT_LPAR PT_SOLID IP_B PT_RPAR NP  ((true,IP_B),NP)
     | PT_DOUBLE IP_B NP                 ((false,IP_B),NP)
     | PT_LPAR PT_DOUBLE IP_B PT_RPAR NP ((false,IP_B),NP)


(* complete path having just one incomplete path possibly preceded by / or //,
   possibly negated *)
CP_C: CP_B                               ([(true,#1 CP_B)],#2 CP_B)
    | PT_NOT CP_B                        ([(false,#1 CP_B)],#2 CP_B)

PAT_A : 
    (* complete path consisting of just one incomplete path *)
        CP_C                              (CP_C)
        (*allows paramthesis before the !*)
      | PT_LPAR PT_NOT IP_D PT_RPAR NP    ([(false,IP_D)],NP)

    (* complete path having at least two incomplete paths *)
      | PT_LPAR IP_E PT_AMPERSAND IP_F PT_RPAR NP (IP_E::IP_F,NP)

START : PATS                           (PATS)

PATS : PAT                             ([PAT])
     | PAT PT_OR PATS                  (PAT::PATS)

PAT  : PAT_A                           (nil,(true,PAT_A))
     | PQS PAT_A                       (PQS,(true,PAT_A)) (*!!!*)
     | NP                              (nil,(true,(nil,NP)))
     | PT_SOLID NP                     (nil,(true,(nil,NP)))
     | PT_DOUBLE NP                    (nil,(false,(nil,NP)))
     | PQS PT_SOLID NP                 (PQS,(true,(nil,NP)))
     | PQS PT_DOUBLE NP                (PQS,(false,(nil,NP)))

PQS  : PT_LBRACK PQ PT_RBRACK          ([PQ])
     | PT_LBRACK PQ PT_RBRACK PQS      (PQ::PQS)

PQ   : FP                              (true,FP)
     | PT_NOT FP                       (false,FP)
