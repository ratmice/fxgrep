signature MatchReport =
   sig
      type Report

      val nullReport   : Report
      val report       : DocDtd.Dtd -> MatchData.Match * Report -> Report
      val reportStart  : string -> Report
      val reportFinish : Report -> unit
   end

structure MatchReport : MatchReport =
   struct
      open GrepError MatchOptions MatchOutput Encoding UtilError

      type Report = int * File option

      val nullReport = (0,NONE) : Report

      fun reportString (s,(c,fopt)) = 
	 case fopt
	   of NONE => (c,fopt)
	    | SOME f => (c,SOME (putString (f,s)))

      fun report dtd (match,(c,fopt)) = 
	 case fopt
	   of NONE => (c+1,fopt)
	    | SOME f => (c+1,SOME (putMatch dtd (f,match)))

      fun reportStart enc =
	 let val p = if not (!O_DO_OUTPUT) then NONE 
		     else SOME (openFile enc) 
			handle NoSuchFile fmsg => NONE before nofileError fmsg
	 in (0,p)
	 end
      
      fun reportFinish (c,fopt) =
         let val _ = case fopt
                       of NONE => ()
                        | SOME f => closeFile f
         in if not (!O_DO_COUNT) then ()
            else app print [Int.toString c," match",if c=1 then "" else "es"," found.\n"]
         end

   end
