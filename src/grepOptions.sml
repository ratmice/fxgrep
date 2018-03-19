signature GrepOptions =
   sig
      include CatOptions

      val O_SILENT          : bool ref
      val O_ERROR_DEVICE    : TextIO.outstream ref
      val O_ERROR_LINEWIDTH : int ref
      val O_GREP_DEBUG      : int ref

      val grepUsage : Options.Usage

      val setGrepDefaults : unit -> unit
      val setGrepOptions  : Options.Option list * (string -> unit) 
	 -> bool * bool * string option * string option
   end

structure GrepOptions : GrepOptions =
   struct
      structure CatOptions = CatOptions()
      open CatOptions Options
 
      val _ = SMLofNJ.Internals.GC.messages false

      val O_SILENT               = ref false
      val O_ERROR_DEVICE         = ref TextIO.stdErr
      val O_ERROR_LINEWIDTH      = ref 80 
      val O_GREP_DEBUG           = ref 0

      val grepUsage = 
         catalogUsage@
         [U_SEP,
          U_ITEM(["-s","--silent"],"Suppress reporting of errors and warnings"),
          U_ITEM(["-e <file>","--error-output=<file>"],"Redirect errors to file (stderr)"),
          U_SEP,
          U_ITEM(["--version"],"Print the version number and exit"),
          U_ITEM(["-?","--help"],"Print this text and exit"),
          U_ITEM(["--"],"Do not recognize remaining arguments as options")
          ]

      fun setGrepDefaults () = 
	 let 
	    val _ = setCatalogDefaults ()

            val _ = O_SILENT               := false
            val _ = O_ERROR_DEVICE         := TextIO.stdErr
	 in ()
	 end

      fun setGrepOptions (opts,optError) =
	 let
            fun onlyOne what = "at most one "^what^" may be specified"
            fun unknown pre opt = String.concat ["unknown option ",pre,opt]
            fun hasNoArg pre key = String.concat ["option ",pre,key," expects no argument"]
            fun mustHave pre key = String.concat ["option ",pre,key," must have an argument"]
            fun mustBeNum pre key = String.concat 
               ["the argument to option ",pre,key," must be a number"]

            fun check_noarg(key,valOpt) = 
               if isSome valOpt then optError (hasNoArg "--" key) else () 

	    fun do_long (pars as (v,h,e,f)) (key,valOpt) =
	       case key 
		 of "help" => (v,true,e,f) before check_noarg(key,valOpt)
		  | "version" => (true,h,e,f) before check_noarg(key,valOpt)
                  | "silent" => pars before O_SILENT := true before check_noarg(key,valOpt)
		  | "error-output" => (case valOpt
					 of NONE => pars before optError (mustHave "--" key)
					  | SOME s => (v,h,SOME s,f))
		  | "debug" => (case valOpt
                                  of NONE => pars before optError (mustHave "--" key)
                                   | SOME s => case Int.fromString s
                                                 of NONE => pars before 
                                                    optError (mustBeNum "--" key)
                                                  | SOME n => pars before O_GREP_DEBUG := n)
		  | _ => pars before optError(unknown "--" key)
		    
	    fun do_short (pars as (v,h,e,f)) (cs,opts) =
	       case cs 
		 of nil => doit pars opts
		  | [#"e"] => (case opts 
				 of OPT_STRING s::opts1 => doit (v,h,SOME s,f) opts1
				  | _ => (optError (mustHave "-" "e"); doit pars opts))
  		  | cs => doit (foldr
				(fn (c,pars) 
				 => case c
				      of #"s" => pars before O_SILENT := true
				       | #"e" => pars before optError (mustHave "-" "e")
				       | #"?" => (v,true,e,f)
				       | c => pars before 
					 optError(unknown "-" (String.implode [c])))
				pars cs) opts
		    
	    and doit pars nil = pars
	      | doit (pars as (v,h,e,f)) (opt::opts) =
	       case opt 
		 of OPT_LONG(key,valOpt) => doit (do_long pars (key,valOpt)) opts
		  | OPT_SHORT cs => do_short pars (cs,opts)
		  | OPT_STRING s => if isSome f 
				       then let val _ = optError(onlyOne "input file") 
					    in doit pars opts
					    end
				    else doit (v,h,e,SOME s) opts
		  | OPT_NOOPT => doit pars opts
		  | OPT_NEG cs => let val _ = if null cs then ()
					      else app (fn c => optError
							(unknown "-n" (String.implode[c]))) cs
				  in doit pars opts
				  end
	    
	    val opts1 = setCatalogOptions (opts,optError)
	 in 
	    doit (false,false,NONE,NONE) opts1
	 end
   end
