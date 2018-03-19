signature GrammarFile = 
   sig
      type File
      type Position
         
      val openFile  : Uri.Uri -> File 
      val closeFile : File -> unit
      val getChar   : File -> UniChar.Char * File
      val ungetChar : File * UniChar.Char -> File
      val getPos    : File -> Errors.Position
   end

structure GrammarFile : GrammarFile = 
   struct
      open GrepError Decode Encoding Errors UniChar Uri

      val THIS_MODULE = "GrammarFile"

      val errorBadChar = errorBadChar "grammar"

      (* column, line, break *)  
      type PosInfo = int * int * bool
      val startPos = (1,1,false)

      type File = DecFile * PosInfo * Char option

      fun getPos (dec,(col,line,_),_) = (decName dec,line,col)
      fun openFile uri = (decOpenUni(SOME uri,UTF8),startPos,NONE)
      fun closeFile (dec,_,_) = ignore (decClose dec)

      fun getChar (f as (dec,(col,line,brk),opt)) =
         case opt 
           of SOME c => (c,(dec,(col,line,brk),NONE))
            | NONE => let val (c,dec1) = decGetChar dec
                      in case c
                           of 0wx09 => (c,(dec1,(col+1,line,false),NONE))
                            | 0wx0A => if brk then getChar(dec1,(col,line,false),NONE)
                                       else (c,(dec1,(1,line+1,false),NONE))
                            | 0wx0D => (0wx0A,(dec1,(1,line+1,true),NONE))
                            | _     => if c>=0wx20 then (c,(dec1,(col+1,line,false),NONE))
                                       else let val _ = errorBadChar (getPos f) c
                                            in getChar(dec1,(col+1,line,false),NONE) 
                                            end
                      end 
                         handle DecEof dec => (0wx00,(dec,(col,line,brk),NONE))
                              | DecError(dec,_,err) 
                            => let val _ = printError "grammar " (getPos f,ERR_DECODE_ERROR err)
                               in getChar(dec,(col,line,false),NONE)
                               end
                            
      fun ungetChar ((dec,info,opt),c) =
         case opt 
           of SOME c => raise InternalError(THIS_MODULE,"ungetChar","double unget")
            | NONE => (dec,info,SOME c)
   end
