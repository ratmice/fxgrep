signature Match = 
   sig
      val parseDoc : DocDtd.Dtd * Uri.Uri option -> int * string * MatchData.Content
      val match    : DocDtd.Dtd * Uri.Uri option -> (bool * MatchData.Passes) -> unit
   end

structure Match : Match =
   struct
      structure ParseDoc = Parse (structure Dtd = DocDtd0
				  structure Hooks = DocHooks0
				  structure Resolve = GrepResolve
				  structure ParserOptions = MatchOptions)
	 
      fun parseDoc (dtd,uri) = 
	 ParseDoc.parseDocument uri (SOME dtd) (DocHooks.docStart dtd)

      structure MatchDoc = Parse (structure Dtd = DocDtd0
				  structure Hooks = MatchHooks0
				  structure Resolve = GrepResolve
				  structure ParserOptions = MatchOptions)
      structure Match2Doc = Parse (structure Dtd = DocDtd0
				  structure Hooks = Match2Hooks0
				  structure Resolve = GrepResolve
				  structure ParserOptions = MatchOptions)
	 
      open GrepOptions MatchData MatchOptions MatchReport

      fun match (dtd,uri) (isContentIgnoring,passes) =
	let 
	  val match2 = 
	    let
	      val (doMatches,doMatches') = 
		case passes of
		  SINGLE (yVec,sigVec,rhsVec,tpVec,otherRules,
			  otherY0s,q0,doMatch,ys_of_y,regexpNameRules,
			  preForm,preFormAfterTag,preFormAfterAtts,postForm)
		  => Vector.sub(doMatch,0)
		| DOUBLE (sigVec,yVec,rhsVec,tpVec,otherRules,
			  otherY0s,qr0,ql0info,doMatch,
			  incomingXVec,regExpNameRules,ys_of_y,form)
		  => Vector.sub(doMatch,0)
	    in
	      (Vector.length doMatches') > 0
	    end

	  val _ = 
	    if !O_GREP_DEBUG <> 1 then ()
	    else 
	      let
		val _ = if match2 then print "Matching pairs.\n\n"
			else ()
		val _ =
		  case passes of 
		    SINGLE _ => app print 
		      ["Single pass ",
		       if !O_MATCH_IN_HOOKS then "while" else "after"," parsing.\n\n"]
		  | DOUBLE _ => print "Two passes.\n\n"
	      in
		()
	      end

	  val  _ = 
	    case passes of 
	      SINGLE p =>
		if not (!O_MATCH_IN_HOOKS) then
		  if match2 then
		      let
			val (noNodes,enc,doc) = parseDoc (dtd,uri)
		      in
			Match2Alg.matchAlg p (enc,doc) (Match2.printMatchTable dtd) dtd
		      end
		    else
		      let
			val (noNodes,enc,doc) = parseDoc (dtd,uri)
			val r0 = reportStart enc
			val r1 = MatchAlg.matchAlg (isContentIgnoring,p) (report dtd) r0 doc dtd
		      in
			MatchReport.reportFinish r1
		      end
		  else
		    if match2 then 
		      Match2Doc.parseDocument uri (SOME dtd) 
		      (Match2Hooks.matchStart (dtd,p))
		    else		      
		      MatchDoc.parseDocument uri (SOME dtd) 
		      (MatchHooks.matchStart (dtd,p))

	    | DOUBLE p => 
		      if match2 then 
			let
			  val (noNodes,enc,doc) = parseDoc (dtd,uri)
			in
			  Match2ArgBlg.matchArgBlg (p:PreArgBlg.PreArgBlg) (enc,doc) 
			  (Match2.printMatchTable dtd) dtd
			end
		      else 
			let
			  val (noNodes,enc,doc) = parseDoc (dtd,uri)
			  val r0 = reportStart enc
			  val r1 = MatchArgBlg.matchArgBlg (p:PreArgBlg.PreArgBlg) (report dtd) r0 doc dtd
			in
			  MatchReport.reportFinish r1    
			end 

	in
	  ()
	end
   end
