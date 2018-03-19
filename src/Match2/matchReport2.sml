signature MatchReport2 =
   sig
      type Report

      val nullReport   : Report
      val report      : DocDtd.Dtd -> (MatchData.Match * NodeSet.set IntListMap.map) * Report -> 
	Report
      val reportStart  : string -> Report
      val reportFinish : int * Report -> unit
   end

structure MatchReport2 : MatchReport2 =
   struct
      open GrepError MatchOptions MatchOutput Encoding UtilError

      type Report = File option

      val nullReport = NONE : Report

      fun report dtd ((primary,secondaries),fopt) = 
	 case fopt
	   of NONE => fopt
	    | SOME f => SOME (putMatch2 dtd (f,(primary,secondaries)))

      fun reportStart enc =
	if not (!O_DO_OUTPUT) then NONE 
	else SOME (openFile enc) 
	  handle NoSuchFile fmsg => NONE before nofileError fmsg
      
      fun reportFinish (c,fopt) =
         let val _ = case fopt
                       of NONE => ()
                        | SOME f => closeFile f
         in if not (!O_DO_COUNT) then ()
            else app print [Int.toString c," binary match",if c=1 then "" else "es"," found.\n"]
         end

   end
