signature GramHooks =
  sig
    exception SpecError of Errors.Position * string
    type AppData
    type AppFinal = GramData.Grammar * GramData.MatchSpec
    val grammarStart : DocDtd.Dtd * GramTables.XTable -> AppData
  end

structure GramHooks0 =
  struct

    open
      Errors HookData IgnoreHooks UniChar UniClasses
      GramData GrepError GramOptions GramTables GramUtil
      GrammarDtd GrammarParser MatchData
      
    val THIS_MODULE = "GramHooks"
      
    exception SpecError of Position * string
    
    type AppFinal = GramData.Grammar * GramData.MatchSpec
    type AppData = 
      XTable * DocDtd.Dtd *
      (Position * Tree) list * (Position * Vector) list 
      * (Position * int * AttSpc vector * (Position * Tree) list) list

    fun hasAtt attIdx (atts:AttSpc vector) =
      Vector.foldl
      (fn ((i,att),opt) =>
       if isSome opt then opt
       else if i = attIdx then SOME att
	    else opt) NONE atts
      
    val hasVarAtt = hasAtt varIdx
    val hasSignAtt = hasAtt signIdx

	 
    fun grammarStart (dtd,tab) = (tab,dtd,nil,nil,nil)

    fun hookXml((tab,dtd,content,vecs,stack),(_,enc,opt)) = (tab,dtd,content,vecs,stack)

    fun posOf (pos,_) = pos
      
    fun takeData (content,vecs) = 
      let 
	val vecs = rev vecs
	val vec = Vector.concat (map #2 vecs)
      in 
	if Vector.length vec=0 then content
	else (posOf(hd vecs),T_TEXT vec)::content
      end

      fun hookStartTag ((tab,dtd,content,vecs,stack),((pos,_),elem,atts,_,mt))  =
	let 
	  val content1 = takeData (content,vecs)
	  val attspecs = List.mapPartial 
	    (fn (i,ap,_) => case ap of 
	     AP_DEFAULT(_,av,_) => SOME(i,av)
	   | AP_PRESENT(_,av,_) => SOME(i,av)
	   | _ => NONE) atts
	  val attvec = Vector.fromList attspecs
	in 
	  if mt then (tab,dtd,(pos,T_ELEM(elem,attvec,emptyContent))::content1,nil,stack)
	  else (tab,dtd,nil,nil,(pos,elem,attvec,content1)::stack)
	 end

      fun hookEndTag ((tab,dtd,content,vecs,stack),_) =
	case stack of 
	  nil => raise InternalError (THIS_MODULE,"hookEndTag","empty stack")
	| (pos,elem,attspecs,content1)::stack1 =>
	    let 
	      val content2 = takeData (content,vecs)	
	      val tree = T_ELEM(elem,attspecs,Vector.fromList(rev content2))
	    in 
	      (tab,dtd,(pos,tree)::content1,nil,stack1)
	    end

      fun hookProcInst ((tab,dtd,content,vecs,stack),((pos,_),target,tpos,text)) =
	let 
	  val content1 = takeData (content,vecs)
	  val tree = T_PI(Data2Vector target,Vector.fromList[(tpos,T_TEXT text)])
	in 
	  (tab,dtd,(pos,tree)::content,nil,stack)
	end
      
      fun addData ((tab,dtd,content,vecs,stack),pos,vec) = (tab,dtd,content,(pos,vec)::vecs,stack)
	
      fun hookData (a,((pos,_),vec,_)) = addData(a,pos,vec)
      fun hookCData (a,((pos,_),vec)) = addData(a,pos,vec)
      fun hookCharRef (a,((pos,_),c,_)) = addData(a,pos,Vector.fromList [c])

    fun normAttValue av =
      let 
	fun doOne nil = nil
	  | doOne (c::cs) = if c=0wx20 then doAll true cs
			    else c::doOne cs
	and doAll addS nil = nil
	  | doAll addS (c::cs) = 
	  if c=0wx20 then doAll addS cs
	  else let 
		 val ys = doOne cs
	       in 
		 if addS then 0wx20::c::ys else c::ys
	       end
      in 
	doAll false av
      end
    fun isaName nil = false
      | isaName (c::cs) = isNms c andalso List.all isName cs
    fun getVar cv = 
      let val norm = normAttValue (Vector2Data cv)
      in if isaName norm then SOME (Data2Vector norm) else NONE
      end


      fun hookFinish ((tab,dtd,content,vecs,stack):AppData) = 
	let
	  val content1 = takeData (content,vecs)
	  val content =
	    case stack of 
	      nil => Vector.fromList (rev content1)
	    | _ => raise InternalError (THIS_MODULE,"hookFinish","non-empty stack")

	  fun getTextContent elIdx cont = 
	    Vector.foldr
	    (fn ((pos,tree),segs) =>
	     case tree of
	       T_ELEM _ => raise SpecError 
		 (pos,
		  (UniChar.Vector2String (Index2X tab elIdx))^
		  " element must have only text content")
	     | T_PI _ => segs
	     | T_TEXT txt => (SEG_DATA (txt,pos))::segs)
	    nil cont

	  fun doTargets (pos,elIdx,atts,cont) =
	    let
	      val segs = getTextContent elIdx cont
	      val targets = parseTargets (dtd,tab) (pos,segs)
	      val targets = ListMergeSort.sort Int.> targets
	    in
	      targets
	    end

	    
	  fun doElem ((pos,tree),g as (fes,targs,targs',form)) = 
	    case tree of
	      T_ELEM (elIdx,atts,cont) =>
		if elIdx = ruleIdx then 
		  case hasVarAtt atts of
		    NONE => g
		  | SOME x => 
		      (case getVar x of
			 NONE => g
		       | SOME x =>
			   let 
			     val segs = getTextContent elIdx cont
			     val idx = declareX tab x
			     val rhs = parseRule (dtd,tab) (pos,segs)
			     val _ = defineX tab (idx,rhs)
			   in 
			     g
			   end
			 handle ParseError => raise SpecError (pos,"parse error in rule"))
		else if elIdx = startIdx then
		  let
		    val segs = getTextContent elIdx cont
		    val fe = parseFexp (dtd,tab) (pos,segs)
		  in
		    (fe::fes,targs,targs',form)
		  end
		     else if elIdx = targetIdx then
		       let
			 val targets = doTargets (pos,elIdx,atts,cont)
		       in
			 (fes,targets,targs',form) (* only the last specified counts *)
		       end
			  else if elIdx = secondaryTargetIdx then
			    let
			      val (form1,targets) = 
				Vector.foldl
				(fn ((pos,tree),(form,targets)) => 
				 case tree of
				   T_ELEM (elIdx,atts,cont) =>
				     if elIdx = formIdx then 
				       let
					 val segs = getTextContent elIdx cont
					 val form = parseFormula (dtd,tab) (pos,segs)
				       in
					 (SOME form,targets)
				       end
				     else if elIdx = targetIdx then (form,doTargets (pos,elIdx,atts,cont))
					  else (form,targets)
				 | _ => (form,targets))
				(NONE,nil)
				cont
			      val form1 = case form1 of
				SOME f => f
			      | NONE => raise SpecError (pos,"no formula was specified")
			    in
			      (fes,targs,(form1,targets)::targs',form)
			    end
			       else if elIdx = formIdx then
				 let
				   val segs = getTextContent elIdx cont
				   val form = parseFormula (dtd,tab) (pos,segs)
				 in
				   (fes,targs,targs',SOME form)
				 end
				    else g
	    | _ => g

	  fun doRoot ((pos,tree),g) =
	    case tree of
	      T_ELEM (elIdx,atts,cont) =>
		if elIdx = grammarIdx then Vector.foldl doElem g cont
		else raise SpecError (pos,"root element must be a grammar")
	    | T_TEXT _ => g
	    | T_PI _ => g	  

	  val (fes,targs,targs',form) = Vector.foldl doRoot (nil,nil,nil,NONE) content
	  val form = case form of
	    SOME f => f
	  | NONE => raise SpecError (("",0,0),"no formula was specified")
	  val targets' = rev targs' 
	  val (max,rules) = extractXTable tab
	in
	  ((max,rev fes,rules),((form,targs),targets'))
	end
      
      fun hookWarning (a,warn) = a before printWarning "" warn
      fun hookError (a,err) = 
	let 
	  val _ = printError "" err
	  val _ = case err of 
	    (_,ERR_NO_SUCH_FILE _) => raise SpecError (("",0,0),"file not found")
	  | _ => ()
	in a
	end
  end

structure GramHooks = GramHooks0 : GramHooks