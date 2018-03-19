signature MatchOutput =
   sig
      type File
      val closeFile   : File -> unit
      val openFile    : string -> File
      val putString   : File * string -> File
      val putMatch    : DocDtd.Dtd -> File * MatchData.Match -> File
      val putMatch2    : DocDtd.Dtd -> 
	File * (MatchData.Match * NodeSet.set IntListMap.map) -> File
   end

structure MatchOutput : MatchOutput =
   struct
      open 
	 UniChar Encode Encoding Errors UtilError UtilString
	 DocDtd GrepError MatchData MatchOptions 

      type File = EncFile
      fun closeFile f = encCloseFile f 
      val validChar = encValidChar

      fun putChar(f,c) = encPutChar(f,c) 
	 handle EncodeError(fname,msg) => encAdapt(f,fname) before encodeError msg

      fun putData(f,cs) = foldl (fn (c,f) => putChar(f,c)) f cs
      fun putVector(f,cv) = Vector.foldl (fn (c,f) => putChar(f,c)) f cv
      fun putString(f,str) = putData(f,String2Data str)
	 
      fun openFile encName = 
	 let val (enc1,encName1) = case !O_OUTPUT_ENCODING
				     of NONE => (isEncoding encName,encName)
				      | SOME x => (isEncoding x,x)
             val f = if enc1<>NOENC then encOpenFile (!O_OUTPUT_FILE,enc1,encName1)
                     else raise NoSuchFile (!O_OUTPUT_FILE,
                                            "Unsupported output encoding \""^encName1^"\"")
         in if not (!O_OUTPUT_TEXTDECL) then f 
            else putString(f,"<?xml version=\"1.0\" encoding=\""^encName1^"\"?>\n\n")
	 end

      fun putNl f = putChar(f,0wx0A)
      fun putBlank f = putChar(f,0wx20)

      val hexDigits = Vector.tabulate(16,fn i => Word.fromInt((if i<10 then 48 else 55)+i))
      fun hexDigit n = Unsafe.Vector.sub(hexDigits,Word.toInt n)
      fun charRefSeq c =
	 if c=0wx00 then [0wx26,0wx23,0wx78,0wx30,0wx3b] (* "&#x0;" *)
	 else let fun mk_hex yet n = if n=0w0 then yet
				     else mk_hex (hexDigit(n mod 0w16)::yet) (n div 0w16)
	      in 0wx26::0wx23::0wx78::mk_hex [0wx3b] c
	      end
      fun putCharRef(f,c) = putData(f,charRefSeq c)
	 
      fun putDataChar(f,c) = 
	 case c 
	   of 0wx26 => putData(f,[0wx26,0wx61,0wx6d,0wx70,0wx3b]) (* "&amp;" *)
	    | 0wx3C => putData(f,[0wx26,0wx6c,0wx74,0wx3b]) (* "&lt;" *)
	    | 0wx3E => putData(f,[0wx26,0wx67,0wx74,0wx3b]) (* "&gt;" *)
	    | _ => if validChar(f,c) then putChar(f,c) else putCharRef(f,c)

      fun putDataVector(f,cv) =
	 Vector.foldl (fn (c,f) => putDataChar(f,c)) f cv

      fun putAttValue (f,cv,q) = 
	 let 
	    fun putOne(c,f) = 
	       case c 
		 of 0wx26 => putData(f,[0wx26,0wx61,0wx6d,0wx70,0wx3b]) (* "&amp;" *)
		  | 0wx3C => putData(f,[0wx26,0wx6c,0wx74,0wx3b]) (* "&lt;" *)
		  | _ => if c<>q andalso validChar(f,c) then putChar(f,c) else putCharRef(f,c)
	    val f1 = putChar(f,q)
	    val f2 = Vector.foldl putOne f1 cv
	    val f3 = putChar(f2,q)
	 in f3
	 end

      fun putTree dtd (f,t) = 
	 case t
	   of T_TEXT txt => putDataVector(f,txt)
	    | T_PI(target,content) => let val f1 = putString (f,"<?")
                                          val f2 = putVector (f1,target)
                                          val f3 = if Vector.length content=0 then f2
                                                   else Vector.foldl 
                                                      (fn ((_,t),f) => putTree dtd (f,t)) 
                                                      (putBlank f2) content
                                          val f4 = putString (f3,"?>")
                                      in f4
				   end
	    | T_ELEM(elem,atts,content) => let val f1 = putString (f,"<")
					       val f2 = putData(f1,Doc2Element dtd elem)
					       val f3 = Vector.foldl
						  (fn ((a,cv),f) 
						   => let val f1 = putBlank f
							  val f2 = putData(f1,Doc2Element dtd a)
							  val f3 = putString(f2,"=")
							  val f4 = putAttValue(f3,cv,0wx27)
						      in f4
						      end) f2 atts
					       val f4 = putString (f3,">")
					       val f5 = Vector.foldl 
						  (fn ((_,t),f) => putTree dtd (f,t)) f4 content
					       val f6 = putString (f5,"</")
					       val f7 = putData(f6,Doc2Element dtd elem)
					       val f8 = putString(f7,">")
					   in f8
					   end

      fun putMatch dtd (f,(pos,t)) = 
	let 
	  val f1 = if not (!O_OUTPUT_POSITION) then f
		   else 
		     let 
		       val f1 = putString (f,"<?fxgrep-match ")
		       val ps = padxRight #"-" (Position2String pos,55)
		       val f2 = putString (f1,ps)
		       val f3 = putString (f2,"?>\n")
		     in 
		       f3
		     end
         in 
	   if !O_POSITION_ONLY then f1
	   else let 
		  val f2 = putTree dtd (f1,t)
		  val f3 = putNl (putNl f2)
		in f3
		end
         end

      fun putMatch2 dtd (f,((pos,t),secondaries)) = 
         let
	   val f = putString (f,"<match>\n") 
	   val indent  = "  "
	   val indent2 = "    "
	   val f = putString (f,indent^"<primary>\n")
	   val f1 = 
	     if not (!O_OUTPUT_POSITION) then f
	     else 
	       putString (f,indent2^"<position>"^(Position2String pos)^"</position>\n")
	   val f2 =
	     if !O_POSITION_ONLY then f1
	     else 
	       let 
		 val f1 = putString (f1,indent2^"<node>")
		 val f2 = putTree dtd (f1,t)
		 val f3 = f2
		 val f4 = putString (f3,"</node>\n")
	       in 
		 f4
	       end
	   val f = putString (f,indent^"</primary>\n")
	   val f3 = 
	     IntListMap.foldli
	     (fn (i,secondaries,f2) =>
	      NodeSet.foldl 
	      (fn ((pos,t),f) =>
	       let
		 (*val f = putString (f,indent^"<secondary%"^(Int.toString i)^">\n")*)
		 val f = putString (f,indent^"<secondary>\n")
		 val f1 =
		   if not (!O_OUTPUT_POSITION) then f
		   else 
		     putString (f,indent2^"<position>"^(Position2String pos)^"</position>\n")
		 val f2 =
		   if !O_POSITION_ONLY then f1
		   else 
		     let 
		       val f1 = putString (f1,indent2^"<node>")
		       val f2 = putTree dtd (f1,t)
		       val f3 = f2
		       val f4 = putString (f3,"</node>\n")
		     in 
		       f4
		     end
		 val f3 = putString (f2,indent^"</secondary>\n")
	       in
		 f2
	       end) f2 secondaries) f2 secondaries
	   val f4 = putString (f3,"</match>\n") 
	 in
	   f4
	 end
   end
