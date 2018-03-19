structure GramData =
   struct
      open RegExp

      (*--------------------------------------------------------------------*)
      (* text patterns are regular expressions over char patterns.          *)   
      (*--------------------------------------------------------------------*)
      datatype CharPattern = 
         CP_START 
       | CP_END
       | CP_POS of CharRanges.CharRange 
       | CP_NEG of CharRanges.CharRange 
      type TextPattern = CharPattern RegExp.RegExp

      (*--------------------------------------------------------------------*)
      (* attribute pattern: present, absent, or matching a text pattern.    *)
      (*--------------------------------------------------------------------*)
      datatype AttPat = 
         AT_NAME of int
       | AT_VALUE of int * TextPattern
      type AttPattern = bool * AttPat

      (*--------------------------------------------------------------------*)
      (* a tag pattern specifies a range of admissible/inadmissible element *)
      (* types and a conjunction of attribute patternss.                    *)
      (*--------------------------------------------------------------------*)
      datatype GiPattern = 
         GI_POS of int list 
       | GI_NEG of int list
       | GI_REG of TextPattern
      type TagPattern = GiPattern * AttPattern list

      (*--------------------------------------------------------------------*)
      (* Regular Expressions over Tree Variables and Forest Expressions.    *)
      (*--------------------------------------------------------------------*)
      type Sign = bool
      type XRegExp = int RegExp.RegExp
      type ForestExp = (Sign * XRegExp) list (*and connencted forest expressions*)
      datatype Rhs =  
         RHS_TEXT of TextPattern
       | RHS_PI of TextPattern * ForestExp
       | RHS_TREE of TagPattern * ForestExp 

      type Primaries = int Formula.Formula * IntLists.IntList 
      type Secondaries = Primaries list
      type MatchSpec = Primaries * Secondaries

      type MultTargets =
	((bool * int list) list * (* primary targets, indexed after match pattern no *)
	 (bool * int list) list list) list (* sec targets indexed after sec order *)

      type Grammar = int * ForestExp list (*starts*)
	* (int * Rhs list) list  (*rules*)
	
      (*--------------------------------------------------------------------*)
      (* This is the input of the grammar parser (grammar.y) ...            *)
      (*--------------------------------------------------------------------*)
      type FlatExp = (Sign * int) list
      datatype FlatRhs = 
         FLAT_TEXT of int option
       | FLAT_ELEM of GiPattern * FlatExp
      type FlatGrammar = int * FlatExp list * (int * FlatRhs list) list (** Targets*)

      (*--------------------------------------------------------------------*)
      (* one node in a path pattern.                                        *)
      (*--------------------------------------------------------------------*)
      datatype NodeTest =
         NT_TRUE
       | NT_GI of GiPattern
       | NT_TEXT of TextPattern
       | NT_PI of TextPattern

      (*--------------------------------------------------------------------*)
      (* qualifiers for a node pattern.                                     *)
      (*--------------------------------------------------------------------*)
      datatype Qualifier = 
         Q_ATT of AttPat
       | Q_CHILDREN of ForestPattern
      and CompletePath =
	CP_NODE of TargetNodePattern
      | CP_OR of CompletePath*CompletePath
      | CP_COMPOSED of IncompletePath*TargetNodePattern
      and TreePattern = 
	TP of bool*CompletePath 
      | HASH
      withtype ForestPattern = TreePattern RegExp.RegExp
      and NodePattern = Errors.Position * NodeTest * (bool * Qualifier) list
      and TargetNodePattern = 
	bool (* true if secondary target *) * NodePattern
      and IncompletePath = TargetNodePattern RegExp1.RegExp

      type TopLevelTreePattern = (bool * (bool * IncompletePath)) list * TargetNodePattern

      type Pattern = ((bool * ForestPattern) list * (bool * TopLevelTreePattern)) list

      (*--------------------------------------------------------------------*)
      (* This specifies whether the input is a grammar or a pattern.        *)
      (*--------------------------------------------------------------------*)
      datatype PatSpec' =
          URI of Uri.Uri
        | STR of string
      datatype PatSpec = 
         GRAMMAR of Uri.Uri
       | PATTERN of PatSpec'
      (*--------------------------------------------------------------------*)
      (* This is the input of the grammar parser (grammar.y) ...            *)
      (*--------------------------------------------------------------------*)
      type PosPos = Errors.Position * Errors.Position
      datatype Segment =
         SEG_CREF of UniChar.Char * Errors.Position 
       | SEG_DATA of UniChar.Vector * Errors.Position
       | SEG_CDATA of UniChar.Vector * Errors.Position
       | SEG_CURRENT of UniChar.Vector * int * int
       | SEG_OTHER of Errors.Position
      type Input = Segment list
      (*--------------------------------------------------------------------*)
      (* ... and this is its output.                                        *)
      (*--------------------------------------------------------------------*)
      datatype YResult = 
         Y_RULE of Rhs 
       | Y_FEXP of ForestExp 
       | Y_TARGET of int list
       | Y_GRAMMAR of Grammar * MatchSpec
       | Y_FORM of int Formula.Formula
   end

