signature GrepError =
   sig
      val hadXmlError    : bool ref
      val hadSyntaxError : bool ref
	 
      val initGramError : unit -> unit

      val yaccError      : string -> string * Errors.Position * Errors.Position -> unit
      val yaccTpError    : Errors.Position -> (string * int * int) -> unit

      val printError     : string -> Errors.Position * Errors.Error -> unit
      val printWarning   : string -> Errors.Position * Errors.Warning -> unit

      val errorBadName   : Errors.Position -> UniChar.Data * UniChar.Data -> unit
      val errorBadChar   : string -> Errors.Position -> UniChar.Char -> unit
      val errorUnclosed  : string -> Errors.Position * Errors.Position -> string -> unit

      val warnUndefined  : Errors.Position list * UniChar.Vector -> unit

      val encodeError    : Encode.EncodeError -> unit
      val nofileError    : string * string -> unit

      val Position2String: Errors.Position -> string
   end

structure GrepError : GrepError = 
   struct
      open CatError UniChar EncodeError Errors GramOptions UtilError UtilString
	 
      val hadXmlError = ref false
      val hadSyntaxError = ref false

      fun Char2Error c = 
	 case c
	   of 0wx9 => "\\t"
	    | 0wxA => "\\n"
	    | _ => if c>=0wx20 andalso c<0wx100 then String.implode [Char2char c]
		   else Char2Uni c

      fun initGramError() = hadXmlError := false before hadSyntaxError := false

      fun lc2String(_,l,c) = String.concat [Int.toString l,".",Int.toString c]	 
      fun flc2String(f,l,c) = String.concat [f,":",Int.toString l,".",Int.toString c]	 
      fun Position2String p = String.concat ["[",flc2String p,"]"]
      fun PosPos2String (p1 as (f1,_,_),p2 as (f2,_,_)) = String.concat 
	 ["[",flc2String p1,"-",if f1=f2 then lc2String p2 else flc2String p2,"]"]
      fun TpPos2String pos (i1,i2) = String.concat 
	 ["[",flc2String pos,"(",Int.toString i1,"-",Int.toString i2,")]"]

      fun printError wher (pos,err) = 
	 let val _ =  hadXmlError := true
	 in if !O_SILENT then () else TextIO.output
	    (!O_ERROR_DEVICE,formatMessage (4,!O_ERROR_LINEWIDTH) 
             (Position2String pos^" "^toUpperFirst(wher^"error")^":"::errorMessage err))
	 end
      fun printWarning wher (pos,warn) = 
         if !O_SILENT then () else TextIO.output
            (!O_ERROR_DEVICE,formatMessage (4,!O_ERROR_LINEWIDTH) 
             (Position2String pos^" "^toUpperFirst(wher^"warning")^":"::warningMessage warn))
            
      fun yaccError wher (msg,p1,p2) = 
	 let val _ = hadSyntaxError := true
	 in if !O_SILENT then () else TextIO.output
	    (!O_ERROR_DEVICE,formatMessage (4,!O_ERROR_LINEWIDTH)
	     [PosPos2String (p1,p2)," ",toUpperFirst wher,msg])
	 end
      fun yaccTpError pos (msg,i1,i2) = 
	 let val _ = hadSyntaxError := true
	 in if !O_SILENT then () else TextIO.output
	    (!O_ERROR_DEVICE,formatMessage (4,!O_ERROR_LINEWIDTH)
	     [TpPos2String pos (i1,i2),"(Text pattern)",toUpperFirst msg])
	 end

      fun lexError wher pos msg = if !O_SILENT then () else TextIO.output
	 (!O_ERROR_DEVICE,formatMessage 
	  (4,!O_ERROR_LINEWIDTH) (Position2String pos^" "^toUpperFirst wher^" error:"::msg))
      fun lexError2 wher pp msg = if !O_SILENT then () else TextIO.output
	 (!O_ERROR_DEVICE,formatMessage 
	  (4,!O_ERROR_LINEWIDTH) (PosPos2String pp^" "^toUpperFirst wher^" error:"::msg))
      fun gramWarning pos msg = 
	let
	  val _ = List.app print msg
	in
if !O_SILENT then () else TextIO.output
	 (!O_ERROR_DEVICE,formatMessage 
	  (4,!O_ERROR_LINEWIDTH) (Position2String pos^" Grammar warning:"::msg))
	end

      fun errorBadChar wher pos c = hadSyntaxError := true before 
	 lexError wher pos ["Illegal character "^Char2Error c] 
      fun errorUnclosed wher pp what = hadSyntaxError := true before 
	 lexError2 wher pp ["Unclosed",what]
      fun errorBadName pos (found,exp) = hadSyntaxError := true before 
	 lexError "grammar syntax" pos 
         ["error: Replacing",quoteErrorData found,"with",quoteErrorData exp]
	 
      fun warnUndefined(ps,var) = gramWarning (hd ps)
	 (["Variable",quoteErrorVector var,"is used here but is not defined"]@
	  (if null (tl ps) then nil
	   else ["(also used at ",List2xString ("",", ",")") Position2String (tl ps)]))

      fun encodeError err = if !O_SILENT then () else TextIO.output
         (!O_ERROR_DEVICE,formatMessage (4,!O_ERROR_LINEWIDTH) 
          ("Encoding error:"::encodeMessage err))
      fun nofileError (f,msg) = TextIO.output
         (!O_ERROR_DEVICE,formatMessage (4,!O_ERROR_LINEWIDTH) 
          ["Cannot open file '"^f^"' for writing. ("^msg^")"])
   end

