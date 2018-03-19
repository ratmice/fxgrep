structure ToDefaultForestPattern =


(*********************************************************************) 
(* Used in pattern parsing to produce canonic forest patterns.       *)
(*                                                                   *)
(* When parsing the decision whether to add possible white spaces    *)
(* and/or arbitrary content to forest patternsis taken in two        *)
(* steps. In the first step it is remembered whether white spaces    *)
(* should be add. In the second pass it is seen whether arbitrary    *)
(* content should be added. Adjacent white spaces and arbitrary      *)
(* content are contracted together to arbitrary content.             *)
(*********************************************************************) 


  struct
    datatype ToDefaultForestPattern =
      BOTH of GramData.ForestPattern
    | LEADING of GramData.ForestPattern
    | TRAILING of GramData.ForestPattern
    | EXACT of GramData.ForestPattern

    fun undefaultedForestPattern tdfp =
      case tdfp of
	BOTH fp => fp
      | LEADING fp => fp
      | TRAILING fp => fp
      | EXACT fp => fp

    fun defaultedForestPattern tdfp =
      let
	val w = GramUtil.FP_WHITE (ErrorData.nullPosition)
      (* w can not be a secondary target, thus the position is not important *)
      in
	case tdfp of
	  BOTH fp => RegExp.makeSeq [w,fp,w]
	| LEADING fp => RegExp.makeSeq [w,fp]
	| TRAILING fp => RegExp.makeSeq [fp,w]
	| EXACT fp => fp
      end
  end