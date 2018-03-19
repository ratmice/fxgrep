signature DocHooks =
   sig
      type AppData
      exception DocFail
      val docStart : DocDtd.Dtd -> AppData
   end

structure DocHooks0 =
   struct
      open DocDtd GrepError Encoding Errors HookData IgnoreHooks MatchData UniChar

      val THIS_MODULE = "DocHooks"

      exception DocFail

      type AppFinal = int * string * Content (*numberOfNodes,encoding,tree*)
      type AppData = 
	int * (*number of nodes*)
	Dtd * 
	string * (*encoding*)
	(Position * Tree) list * (Position * Vector) list 
	* (Position * int * AttSpc vector * (Position * Tree) list) list
	 
      fun docStart dtd = (0,dtd,"UTF-8",nil,nil,nil)

      fun hookXml((c,dtd,_,content,vecs,stack),(_,enc,opt)) =
         let val encName = case opt
                             of SOME(_,SOME encName,_) => encName
                              | _ => encodingName enc
         in (c,dtd,encName,content,vecs,stack)
         end

      fun posOf (pos,_) = pos

      fun takeData (c,content,vecs) = 
	 let 
            val vecs = rev vecs
            val vec = Vector.concat (map #2 vecs)
	 in 
            if Vector.length vec=0 then (c,content )
            else (c+1,(posOf(hd vecs),T_TEXT vec)::content)
	 end

      fun hookStartTag ((c,dtd,enc,content,vecs,stack),((pos,_),elem,atts,_,mt))  =
	 let 
	    val (c,content1) = takeData (c,content,vecs)
	    val attspecs = List.mapPartial 
	      (fn (i,ap,_) => case ap
	       of AP_DEFAULT(_,av,_) => SOME(DocAtt2Elem dtd i,av)
	     | AP_PRESENT(_,av,_) => SOME(DocAtt2Elem dtd i,av)
	     | _ => NONE) atts
	    val attvec = Vector.fromList attspecs
	 in if mt then (c+1,dtd,enc,(pos,T_ELEM(elem,attvec,emptyContent))::content1,nil,stack)
	    else (c+1,dtd,enc,nil,nil,(pos,elem,attvec,content1)::stack)
	 end

      fun hookEndTag ((c,dtd,enc,content,vecs,stack),_) =
	 case stack 
	   of nil => raise InternalError (THIS_MODULE,"hookEndTag","empty stack")
	    | (pos,elem,attspecs,content1)::stack1 =>
	      let 
		 val (c,content2) = takeData (c,content,vecs)	
		 val tree = T_ELEM(elem,attspecs,Vector.fromList(rev content2))
	      in (c,dtd,enc,(pos,tree)::content1,nil,stack1)
	      end

      fun hookProcInst ((c,dtd,enc,content,vecs,stack),((pos,_),target,tpos,text)) =
	 let 
	    val (c,content1) = takeData (c,content,vecs)
	    val tree = T_PI(Data2Vector target,Vector.fromList[(tpos,T_TEXT text)])
	 in (c+1,dtd,enc,(pos,tree)::content,nil,stack)
	 end

      fun addData ((c,dtd,enc,content,vecs,stack),pos,vec) =
	 (c,dtd,enc,content,(pos,vec)::vecs,stack)
      
      fun hookData (a,((pos,_),vec,_)) = addData(a,pos,vec)
      fun hookCData (a,((pos,_),vec)) = addData(a,pos,vec)
      fun hookCharRef (a,((pos,_),c,_)) = addData(a,pos,Vector.fromList [c])

      fun hookFinish (c,dtd,enc,content,vecs,stack) = 
	let
	  val (c,content1) = takeData (c,content,vecs)
	in
	  case stack of 
	    nil => (c,enc,Vector.fromList (rev content1))
	  | _ => raise InternalError (THIS_MODULE,"hookFinish","non-empty stack")
	end

      fun hookWarning (a,warn) = a before printWarning "" warn
      fun hookError (a,err) = 
         let 
            val _ = printError "" err
            val _ = case err 
                      of (_,ERR_NO_SUCH_FILE _) => raise DocFail
                       | _ => ()
         in a
         end
   end
      
structure DocHooks = DocHooks0 : DocHooks