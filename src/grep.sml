signature Grep =
   sig
      val grep : string * string list -> OS.Process.status
   end

structure Grep =
   struct
      open 
	 DocDtd GramOptions GrepOptions Match MatchOptions Options Uri
	 
      val usage = List.concat [matchUsage,[U_SEP],gramUsage,[U_SEP],grepUsage]
	 
      exception Exit of OS.Process.status 
	 
      fun grep(_,args) = 
	 let 
	    val prog = "fxgrep"
	    val hadError = ref false
	 
	    fun optError msg = 
	       let val _ = TextIO.output(TextIO.stdErr,prog^": "^msg^".\n")
	       in hadError := true
	       end
	    fun exitError msg = 
	       let val _ = TextIO.output(TextIO.stdErr,prog^": "^msg^".\n")
	       in raise Exit OS.Process.failure 
	       end
	    fun exitHelp prog = 
	       let val _ = printUsage TextIO.stdOut prog usage
	       in raise Exit OS.Process.success 
	       end
	    fun exitVersion prog = 
	       let val _ = app print [prog," version ",GrepVersion.FXGREP_VERSION,
                                      " using fxlib version ",Version.FXP_VERSION,"\n"]
	       in raise Exit OS.Process.success 
	       end
	    
	    val noInput = "an pattern file must be specified"
	    val noGrammar = "no grammar was specified"
	    val noPattern = "no pattern was specified"
	    fun summOpt prog = "For a summary of options type "^prog^" --help"
	    fun noSuchFile(f,cause) = "can't open file '"^f^"': "^exnMessage cause
	       
	    val opts = parseOptions args
	    val _ = setMatchDefaults()
	    val _ = setGramDefaults()
	    val _ = setGrepDefaults()
	    val opts1 = setMatchOptions (opts,optError)
	    val (specOpt,opts2) = setGramOptions (opts1,optError)
	    val (vers,help,err,file) = setGrepOptions (opts2,optError)

	    val _ = if !hadError then exitError (summOpt prog) else ()
	    val _ = if vers then exitVersion prog else ()
	    val _ = if help then exitHelp prog else ()

	    val _ = case err 
		      of SOME "-" => O_ERROR_DEVICE := TextIO.stdErr
		       | SOME f => (O_ERROR_DEVICE := TextIO.openOut f
				    handle IO.Io {cause,...} => exitError(noSuchFile(f,cause)))
		       | NONE => ()
	    val spec = case specOpt
                       of NONE => exitError noGrammar
                        | SOME spec => spec
	    val uri = case file
                        of NONE => NONE
                         | SOME f => SOME(String2Uri f)


            val (dtd,tab,(g,matchSpec)) = GramParse.parseGrammar spec
               handle GramParse.ParseError => 
		 let 
		   val _ = TextIO.output 
		     (TextIO.stdErr,"fxgrep: Grammar parse error. Check grammar syntax.\n")
		 in
		   (raise Exit OS.Process.failure)
		 end


	    val _ = 
	      if !O_GREP_DEBUG<3 then ()
	      else print (GramString.Grammar2tdString (tab,dtd) (g,matchSpec))

	    val (flat as (g1 as (_,_,rules),xreVec,_,_),(xDontCare,_,_)) = 
	      GramFlatten.flatten' g

	    (*val _ = print (GramString.FlatGrammar2tdString 
			   (fn re => (#1 (Vector.sub(xreVec,re)))) (tab,dtd) (g1,matchSpec))*)

	    val (isContentIgnoring,passes) = 
	      GramAnalyze.analyze (flat,matchSpec,xDontCare)


            val _ = 
	      match (dtd,uri) (isContentIgnoring,passes)
	      handle DocFail => 
		()

	    val _ = if isSome err then TextIO.closeOut (!O_ERROR_DEVICE) else ()
	 in 
	    OS.Process.success
	 end
      handle 
      Exit status => status
    | GramHooks.SpecError (pos,msg) =>
	let 
	  val _ = TextIO.output (TextIO.stdErr,(GrepError.Position2String pos)^": "^msg^".\n")
	in 
	  OS.Process.failure 
	end
    | exn => let 
	       val _ = TextIO.output 
		 (TextIO.stdErr,"fxgrep: Unexpected exception: "^exnMessage exn^".\n")
	     in 
	       OS.Process.failure 
	     end
   end
