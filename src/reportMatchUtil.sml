signature ReportMatchUtil =
   sig
      val reportMatches : 'a MatchData.Collector -> (MatchData.Matches * 'a) -> 'a
   end

structure ReportMatchUtil : ReportMatchUtil =
   struct
      open MatchData

      fun reportMatches reportOne (ms,x) =
         case ms
           of ONE m => reportOne(m,x)
            | MORE(mOpt,ms) => 
              let val x1 = case mOpt
                             of NONE => x
                              | SOME m => reportOne(m,x)
              in foldr (reportMatches reportOne) x1 ms
              end
   end
