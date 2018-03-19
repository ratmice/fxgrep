structure Formula =
  struct
    datatype 'a Formula = 
      VAR of 'a | NOT of 'a Formula |
      AND of 'a Formula * 'a Formula | OR of 'a Formula * 'a Formula

    fun Formula2String X2String form =
      case form of
	VAR x => X2String x
      | NOT f => "!("^(Formula2String X2String f)^")"
      | AND (f1,f2) => "("^(Formula2String X2String f1)^")&("^(Formula2String X2String f2)^")"
      | OR (f1,f2) => "("^(Formula2String X2String f1)^")|("^(Formula2String X2String f2)^")"

    fun formulaVars form =
      case form of
	VAR x => [x]
      | NOT f => formulaVars f
      | AND (f1,f2) => IntLists.cupIntLists(formulaVars f1,formulaVars f2)
      | OR (f1,f2) => IntLists.cupIntLists(formulaVars f1,formulaVars f2)

    fun eval evalX form =
      let
	fun eval1 form =
	  case form of
	    VAR x => evalX x
	  | NOT f => not (eval1 f)
	  | AND (f1,f2) => (eval1 f1) andalso (eval1 f2)
	  | OR (f1,f2) => (eval1 f1) orelse (eval1 f2)
      in
	eval1 form
      end

    fun preFormula form =
      case form of
	VAR x => SOME (VAR x)
      | NOT f => NONE (* corresponds to true *)
      | AND (f1,f2) => 
	  (case preFormula f1 of
	     SOME f1 => 
	       (case preFormula f2 of 
		  SOME f2 => SOME (AND (f1,f2))
		| NONE => SOME f1)
	   | NONE =>
	       (case preFormula f2 of 
		  SOME f2 => SOME f2
		| NONE => NONE))
      | OR (f1,f2)  =>
	  (case preFormula f1 of
	     SOME f1 => 
	       (case preFormula f2 of 
		  SOME f2 => SOME (OR (f1,f2))
		| NONE => NONE)
	   | NONE => NONE)


    fun mapForm f form =
      case form of
	VAR x => VAR (f x)
      | NOT form => NOT (mapForm f form)
      | AND (f1,f2) => AND (mapForm f f1,mapForm f f2)
      | OR (f1,f2) => OR (mapForm f f1,mapForm f f2)
      

  end