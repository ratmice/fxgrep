(*---------------------------------------------------------------------------*)
(* the grammar DTD structure is used for parsing the grammar (xml document). *)
(* It has predefined indices for elements 'rule', 'start' and 'target'       *)
(* as well as for attribute 'var'. It uses the default options.              *)
(*---------------------------------------------------------------------------*)
signature GrammarDtd = 
   sig
      val grammarIdx   : int
      val ruleIdx   : int
      val formIdx  : int
      val startIdx  : int
      val targetIdx : int
      val secondaryTargetIdx : int
      val varIdx    : int
      val signIdx    : int
   end

structure GrammarDtd0 = 
   struct
      open Dtd
	 
      val grammarGi  = UniChar.String2Data "grammar"
      val ruleGi  = UniChar.String2Data "rule"
      val formGi   = UniChar.String2Data "formula"
      val startGi   = UniChar.String2Data "start"
      val targetGi = UniChar.String2Data "targets"
      val secondaryTargetGi = UniChar.String2Data "secondaries"
      val varAtt    = UniChar.String2Data "var"
      val signAtt    = UniChar.String2Data "sign"

      fun initDtdTables () = 
	 let 
	    val dtd = Dtd.initDtdTables()
	    val _ = Element2Index dtd grammarGi
	    val _ = Element2Index dtd ruleGi
	    val _ = Element2Index dtd formGi
	    val _ = Element2Index dtd startGi
	    val _ = Element2Index dtd targetGi
	    val _ = Element2Index dtd secondaryTargetGi
	    val _ = AttNot2Index dtd varAtt
	    val _ = AttNot2Index dtd signAtt
	 in dtd
	 end

      local
	 val dtd = initDtdTables()
      in   
	 val grammarIdx  = Element2Index dtd grammarGi
	 val ruleIdx  = Element2Index dtd ruleGi
	 val startIdx   = Element2Index dtd startGi
	 val formIdx   = Element2Index dtd formGi
	 val targetIdx = Element2Index dtd targetGi
	 val secondaryTargetIdx = Element2Index dtd secondaryTargetGi
	 val varIdx     = AttNot2Index dtd varAtt
	 val signIdx     = AttNot2Index dtd signAtt
      end
   end

structure GrammarDtd = GrammarDtd0 : GrammarDtd
