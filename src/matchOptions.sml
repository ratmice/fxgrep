signature MatchOptions =
   sig
      include GrepOptions
      include ParserOptions
      
      val O_FORCE_SINGLE     : bool ref
      val O_FORCE_DOUBLE     : bool ref
      val O_MATCH_IN_HOOKS   : bool ref
      val O_GEN_INFO_GRAPH   : bool ref

      val O_DO_COUNT         : bool ref
      val O_DO_OUTPUT        : bool ref
      val O_POSITION_ONLY    : bool ref
      val O_OUTPUT_POSITION  : bool ref
      val O_OUTPUT_FILE      : string ref
      val O_OUTPUT_TEXTDECL  : bool ref
      val O_OUTPUT_ENCODING  : string option ref
      val O_MATCH_SELECT     : MatchData.MatchSelect ref

      val setMatchDefaults : unit -> unit
      val setMatchOptions  : Options.Option list * (string -> unit) -> Options.Option list

      val matchUsage : Options.Usage
   end

structure MatchOptions : MatchOptions =
   struct
      structure ParserOptions = ParserOptions()
      open GrepOptions MatchData ParserOptions Options

      val O_FORCE_SINGLE     = ref false
      val O_FORCE_DOUBLE     = ref false
      val O_MATCH_IN_HOOKS   = ref false
      val O_GEN_INFO_GRAPH   = ref false

      val O_DO_COUNT         = ref false
      val O_DO_OUTPUT        = ref true
      val O_POSITION_ONLY    = ref false
      val O_OUTPUT_POSITION  = ref true
      val O_OUTPUT_FILE      = ref "-"
      val O_OUTPUT_ENCODING  = ref NONE : string option ref
      val O_OUTPUT_TEXTDECL  = ref false
      val O_MATCH_SELECT     = ref ALL

      val matchUsage = 
         [U_ITEM(["-n","--no-output"],"Do not generate output"),
          U_ITEM(["-k","--count"],"Count matches but don't generate output"),
          U_ITEM(["-o <file>","--output=<file>"],"Write output to file (stdout)"),
          U_ITEM(["--output-encoding=<enc>"],"Encoding for generated output (input encoding)"),
          U_ITEM(["--output-textdecl[=(yes|no)]"],"Output a text declaration (yes)"),
          U_ITEM(["-np","--no-position"],"Do not output the positions of matches"),
          U_ITEM(["-nt","--position-only"],"Output only the positions of matches"), 
          U_SEP,
          U_ITEM(["-O","--outermost"],"Report only outermost matches"), 
          U_ITEM(["-I","--innermost"],"Report only innermost matches"), 
          U_ITEM(["-A","--all"],"Report all matches (default)"), 
          U_SEP,
	  U_ITEM(["-h","--force-hooks"],
                 "Force matching during parsing in case of a single pass"),
          U_ITEM(["-1","--force-single"],
                 "Force single-pass matching disregarding grammar analysis"),
          U_ITEM(["-2","--force-double"],
                 "Force two-pass matching disregarding grammar analysis"),
          U_SEP
          ]
         @parserUsage

      fun setMatchDefaults () = 
         let 
            val _ = setParserDefaults()
            val _ = O_VALIDATE         := false
               
            val _ = O_DO_COUNT         := false
            val _ = O_DO_OUTPUT        := true
            val _ = O_POSITION_ONLY    := false
            val _ = O_OUTPUT_POSITION  := true
            val _ = O_OUTPUT_FILE      := "-"
            val _ = O_OUTPUT_ENCODING  := NONE
            val _ = O_OUTPUT_TEXTDECL  := false
            val _ = O_MATCH_SELECT     := ALL
            val _ = O_MATCH_IN_HOOKS   := false
	    val _ = O_FORCE_SINGLE     := false
	    val _ = O_FORCE_DOUBLE     := false
         in ()
         end

      fun setMatchOptions (opts,optError) =
         let
            fun hasNoArg pre key = String.concat ["option ",pre,key," expects no argument"]
            fun mustHave pre key = String.concat ["option ",pre,key," must have an argument"]
            fun yesOrNo key = String.concat ["the argument to --",key," must be 'yes' or 'no'"]

            fun check_noarg(key,valOpt) = 
               if isSome valOpt then optError (hasNoArg "--" key) else () 

            fun do_long (key,valOpt) =
               case key 
                 of "no-output" => true before 
                    (O_DO_OUTPUT := false; check_noarg(key,valOpt))
                  | "count" => true before 
                    (O_DO_OUTPUT := false; O_DO_COUNT := true; check_noarg(key,valOpt))
                  | "output" => let val _ = O_DO_OUTPUT := true
                                    val _ = case valOpt
                                              of NONE => ()
                                               | SOME s => O_OUTPUT_FILE := s 
                                in true
                                end
                  | "output-encoding" => let val _ = case valOpt
                                                       of NONE => optError (mustHave "--" key)
                                                        | SOME s => O_OUTPUT_ENCODING := SOME s
                                         in true
                                         end
                  | "output-textdecl" => let val _ = case valOpt
                                                       of NONE => O_OUTPUT_TEXTDECL := true
                                                        | SOME "yes" => O_OUTPUT_TEXTDECL := true
                                                        | SOME "no" => O_OUTPUT_TEXTDECL := false
                                                        | SOME s => optError (yesOrNo key)
                                         in true
                                         end
                  | "no-position" => let val _ =  O_OUTPUT_POSITION := false
                                         val _ = check_noarg(key,valOpt)
                                     in true
                                     end
                  | "position-only" => let val _ =  O_POSITION_ONLY := true
                                           val _ = check_noarg(key,valOpt)
                                       in true
                                       end
                  | "outermost" => let val _ = O_MATCH_SELECT := OUTER
                                       val _ = check_noarg(key,valOpt)
                                   in true
                                   end
                  | "innermost" => let val _ = O_MATCH_SELECT := INNER
                                       val _ = check_noarg(key,valOpt)
                                   in true
                                   end
                  | "all" => let val _ = O_MATCH_SELECT := ALL
                                 val _ = check_noarg(key,valOpt)
                             in true
                             end
                  | "force-single" => let val _ = O_FORCE_SINGLE := true
					  val _ = check_noarg(key,valOpt)
				      in true
				      end
                  | "force-double" => let val _ = O_FORCE_DOUBLE := true
					  val _ = check_noarg(key,valOpt)
				      in true
				      end
                  | "force-hooks" => let val _ = O_MATCH_IN_HOOKS := true
                                         val _ = check_noarg(key,valOpt)
                                     in true
                                     end
                  | _ => false
                        
            fun do_short (cs,opts) =
               case cs 
                 of nil => doit opts
                  | [#"o"] => let val opts1 = case opts 
                                                of OPT_STRING s::opts1 => opts1 
                                                   before O_OUTPUT_FILE := s
                                                 | _ => opts
                                  val _ = O_DO_OUTPUT := true 
                              in doit opts1
                              end
                  | cs => 
                    let val cs1 = List.filter
                       (fn c => case c
                                  of #"n" => false before O_DO_OUTPUT := false
                                   | #"k" => false before 
                                     (O_DO_OUTPUT := false; O_DO_COUNT := true)
                                   | #"o" => false before O_DO_OUTPUT := true
                                   | #"1" => false before O_FORCE_SINGLE := true
                                   | #"2" => false before O_FORCE_DOUBLE := true
                                   | #"h" => false before O_MATCH_IN_HOOKS := true
                                   | #"A" => false before O_MATCH_SELECT := ALL
                                   | #"I" => false before O_MATCH_SELECT := INNER
                                   | #"O" => false before O_MATCH_SELECT := OUTER
                                   | c => true) cs
                    in if null cs1 then doit opts else OPT_SHORT cs1::doit opts 
                    end

            and do_neg (cs,opts) =
               let val cs1 = List.filter
                  (fn c => case c
                             of #"k" => false before O_DO_COUNT := false
                              | #"o" => false before O_DO_OUTPUT := false
                              | #"p" => false before O_OUTPUT_POSITION := false
                              | #"t" => false before (O_OUTPUT_POSITION := true;
                                                      O_POSITION_ONLY := true)
                              | c => true) cs
               in if null cs1 then doit opts else OPT_NEG cs1::doit opts 
               end
                 
            and doit nil = nil
              | doit (opt::opts) =
               case opt 
                 of OPT_LONG(key,valOpt) => if do_long (key,valOpt) then doit opts 
                                            else opt::doit opts
                  | OPT_NEG cs => do_neg (cs,opts)
                  | OPT_SHORT cs => do_short (cs,opts)
                  | _ => opt::doit opts
                                               
            val opts1 = setParserOptions (opts,optError)
         in 
            doit opts1
         end
   end
