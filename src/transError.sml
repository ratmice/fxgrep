signature TransError =
   sig
      val hadSyntaxError : bool ref

      val initTransError : unit -> unit

      val yaccError      : string -> string * Errors.Position * Errors.Position -> unit
      val yaccTpError    : Errors.Position -> (string * int * int) -> unit

      val printError     : Errors.Position * Errors.Error -> unit

      val errorBadName   : Errors.Position -> UniChar.Data * UniChar.Data -> unit
      val errorBadChar   : string -> Errors.Position -> UniChar.Char -> unit
      val errorUnclosed  : string -> Errors.Position * Errors.Position -> string -> unit

      val encodeError    : Encode.EncodeError -> unit
      val nofileError    : string * string -> unit
   end


structure TransError : TransError = 
   struct
      open CatError UniChar EncodeError Errors UtilError UtilString
	 
      val hadSyntaxError = ref false
      val O_ERROR_LINEWIDTH = ref 80

      fun Char2Error c = 
	 case c
	   of 0wx9 => "\\t"
	    | 0wxA => "\\n"
	    | _ => if c>=0wx20 andalso c<0wx100 then String.implode [Char2char c]
		   else Char2Uni c

      fun initTransError() = hadSyntaxError := false

      fun lc2String(_,l,c) = String.concat [Int.toString l,".",Int.toString c]	 
      fun flc2String(f,l,c) = String.concat [f,":",Int.toString l,".",Int.toString c]	 
      fun Position2String p = String.concat ["[",flc2String p,"]"]
      fun PosPos2String (p1 as (f1,_,_),p2 as (f2,_,_)) = String.concat 
	 ["[",flc2String p1,"-",if f1=f2 then lc2String p2 else flc2String p2,"]"]
      fun TpPos2String pos (i1,i2) = String.concat 
	 ["[",flc2String pos,"(",Int.toString i1,"-",Int.toString i2,")]"]

      fun printError (pos,err) = TextIO.output
         (TextIO.stdErr,formatMessage (4,!O_ERROR_LINEWIDTH) 
          (Position2String pos^" Error:"::errorMessage err))

      fun yaccError wher (msg,p1,p2) =  hadSyntaxError := true before TextIO.output
         (TextIO.stdErr,formatMessage (4,!O_ERROR_LINEWIDTH)
          [PosPos2String (p1,p2)," ",toUpperFirst wher,msg])
      fun yaccTpError pos (msg,i1,i2) = hadSyntaxError := true before TextIO.output
         (TextIO.stdErr,formatMessage (4,!O_ERROR_LINEWIDTH)
          [TpPos2String pos (i1,i2),"(Text pattern)",toUpperFirst msg])
         
      fun lexError wher pos msg = TextIO.output
	 (TextIO.stdErr,formatMessage 
	  (4,!O_ERROR_LINEWIDTH) (Position2String pos^" "^toUpperFirst wher^" error:"::msg))
      fun lexError2 wher pp msg = TextIO.output
	 (TextIO.stdErr,formatMessage 
	  (4,!O_ERROR_LINEWIDTH) (PosPos2String pp^" "^toUpperFirst wher^" error:"::msg))

      fun errorBadChar wher pos c = hadSyntaxError := true before 
	 lexError wher pos ["Illegal character "^Char2Error c] 
      fun errorUnclosed wher pp what = hadSyntaxError := true before 
	 lexError2 wher pp ["Unclosed",what]
      fun errorBadName pos (found,exp) = hadSyntaxError := true before 
	 lexError "grammar syntax" pos 
         ["error: Replacing",quoteErrorData found,"with",quoteErrorData exp]
	 
      fun encodeError err = TextIO.output
         (TextIO.stdErr,formatMessage (4,!O_ERROR_LINEWIDTH) 
          ("Encoding error:"::encodeMessage err))
      fun nofileError (f,msg) = TextIO.output
         (TextIO.stdErr,formatMessage (4,!O_ERROR_LINEWIDTH) 
          ["Cannot open file '"^f^"' for writing. ("^msg^")"])
   end

