signature GramOptions =
   sig
      include GrepOptions
      include ParserOptions

      val O_WARN_UNDEFINED       : bool ref
      val O_IGNORE_XML_ERRORS    : bool ref
      val O_IGNORE_SYNTAX_ERRORS : bool ref

      val O_TS_TREEVAR           : int ref 

      val setGramDefaults : unit -> unit
      val setGramOptions  : Options.Option list * (string -> unit) 
         -> GramData.PatSpec option * Options.Option list

      val gramUsage : Options.Usage
   end      

structure GramOptions : GramOptions = 
   struct
      open Options GramData GrepOptions

      structure ParserOptions = ParserOptions ()
      open ParserOptions
 
      val O_GRAMMAR_DEBUG        = ref false
      val O_WARN_UNDEFINED       = ref false
      val O_IGNORE_XML_ERRORS    = ref true
      val O_IGNORE_SYNTAX_ERRORS = ref false

      val O_TS_TREEVAR  = ref 4

      fun setGramDefaults () =
         let 
            val _ = setParserDefaults()
               
            val _ = O_VALIDATE := false
            val _ = O_COMPATIBILITY := false
            val _ = O_INCLUDE_EXT_PARSED := true

            val _ = O_WARN_UNDEFINED       := false
            val _ = O_IGNORE_XML_ERRORS    := true
            val _ = O_IGNORE_SYNTAX_ERRORS := false
         in ()
         end

      val _ = setGramDefaults()

      val gramUsage = 
         [U_ITEM(["-P <pat>"],"Use pattern <pat>"),
          U_ITEM(["-p <file>","--pattern=<file>"],"Read pattern from file <file>"),
          U_ITEM(["-g <file>","--grammar=<file>"],"Read grammar from file <file>"),
          U_SEP,
          U_ITEM(["--grammar-validate[=(yes|no)]"],"Validate grammar if in XML format (no)"),
          U_ITEM(["--grammar-include[=(yes|no)]"],"Include external entities in grammar (yes)"),
          U_SEP,
          U_ITEM(["--warn-undef-vars[=(yes|no)]"],"Warn about undefined variables (no)"),
          U_ITEM(["--ignore-xml-errors[=(yes|no)]"],
                 "Continue if the grammar has XML errors (yes)"),
          U_ITEM(["--ignore-syntax-errors=[(yes|no)]"],
                 "Try to continue if the grammar or pattern has syntax errors (no)")
          ]

      fun setGramOptions (opts,optError) =
         let
            val onlyOne = "at most one pattern or grammar may be specified"
            fun hasNoArg pre key = String.concat ["option ",pre,key," expects no argument"]
            fun mustHave pre key = String.concat ["option ",pre,key," must have an argument"]
            fun yesOrNo key = String.concat ["the argument to --",key," must be 'yes' or 'no'"]

            fun check_noarg(key,valOpt) = 
               if isSome valOpt then optError (hasNoArg "--" key) else () 

            fun do_yesno(key,valOpt,flag) = 
               case valOpt
                 of NONE => flag := true
                  | SOME "no" => flag := false
                  | SOME "yes" => flag := true
                  | SOME s => optError (yesOrNo key)
                    
            fun do_long g (key,valOpt) =
               case key 
                 of "pattern" => 
                    let val g1 = case valOpt
                                   of NONE => g before optError (mustHave "--" key)
                                    | SOME s => case g 
                                                  of NONE => SOME(PATTERN(URI(Uri.String2Uri s)))
                                                   | _ => g before optError onlyOne
                    in (g1,true)
                    end
                  | "grammar" => 
                    let val g1 = case valOpt
                                   of NONE => g before optError (mustHave "--" key)
                                    | SOME s => case g 
                                                  of NONE => SOME(GRAMMAR(Uri.String2Uri s))
                                                   | _ => g before optError onlyOne
                    in (g1,true)
                    end
                  | "grammar-validate" => 
                        (g,true) before do_yesno(key,valOpt,O_VALIDATE)
                  | "grammar-include" => 
                        (g,true) before do_yesno(key,valOpt,O_INCLUDE_EXT_PARSED)
                  | "warn-undef-vars" => 
                        (g,true) before do_yesno(key,valOpt,O_WARN_UNDEFINED)
                  | "ignore-xml-errors" => 
                        (g,true) before do_yesno(key,valOpt,O_IGNORE_XML_ERRORS)
                  | "ignore-syntax-errors" => 
                        (g,true) before do_yesno(key,valOpt,O_IGNORE_SYNTAX_ERRORS)
                  | _ => (g,false)
                        
            fun do_gram g opts = 
               case opts 
                 of OPT_STRING s::opts1 =>
                    let val g1 = case g
                                   of NONE => SOME(GRAMMAR(Uri.String2Uri s))
                                    | _ => g before optError onlyOne
                    in doit g1 opts1
                    end
                  | _ => (optError (mustHave "-" "g"); doit g opts)

            and do_pat_arg g opts = 
               case opts 
                 of OPT_STRING s::opts1 =>
                    let val g1 = case g
                                   of NONE => SOME(PATTERN(STR s))
                                    | _ => g before optError onlyOne
                    in doit g1 opts1
                    end
                  | _ => (optError (mustHave "-" "P"); doit g opts)

            and do_pat_uri g opts = 
               case opts 
                 of OPT_STRING s::opts1 =>
                    let val g1 = case g
                                   of NONE => SOME(PATTERN(URI(Uri.String2Uri s)))
                                    | _ => g before optError onlyOne
                    in doit g1 opts1
                    end
                  | _ => (optError (mustHave "-" "p"); doit g opts)

            and do_short g (cs,opts) =
               case cs 
                 of nil => doit g opts
                  | [#"g"] => do_gram g opts 
                  | [#"p"] => do_pat_uri g opts 
                  | [#"P"] => do_pat_arg g opts 
                  | cs => 
                    let val cs1 = List.filter
                       (fn #"g" => false before optError (mustHave "-" "g")
                         | _ => true) cs
                    in if null cs1 then doit g opts 
                       else let val (g1,opts1) = doit g opts
                            in (g1,OPT_SHORT cs1::opts1)
                            end
                    end
                 
            and doit g nil = (g,nil)
              | doit g (opt::opts) =
               case opt 
                 of OPT_LONG(key,valOpt) => 
                    let val (g1,taken) = do_long g (key,valOpt)
                    in if taken then doit g1 opts 
                       else let val (g2,opts2) = doit g1 opts
                            in (g2,opt::opts2)
                            end
                    end
                  | OPT_SHORT cs => do_short g (cs,opts)
                  | _ => let val (g1,opts1) = doit g opts
                         in (g1,opt::opts1)
                         end
         in doit NONE opts
         end
   end
