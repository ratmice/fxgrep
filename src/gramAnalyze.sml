signature GramAnalyze =
  sig
    val analyze : GramFlatten.Flat * GramData.MatchSpec * int -> 
      (bool * MatchData.Passes)

    val multAnalyze : GramFlatten.Flat * GramData.MatchSpec list * int * Pre.Intervals -> 
      (bool * MatchData.Passes)
  end

structure GramAnalyze : GramAnalyze =
   struct
      open
         GrepOptions IntLists RegExp 
         GramData GramString GramTables GramUtil MatchData MatchOptions

      val THIS_MODULE = "GramAnalyze"
      
      fun computeOccs ((max,starts,rules),xreVec,_,_) = 
         let 
            val xs_in_re = Vector.map (fn (re,_) => sortInt (regExpSymbols re)) xreVec
               
            val res_of_x = let val arr = Array.array(max,nil)
                               val _ = Vector.appi 
                                  (fn (i,xs) => app 
                                   (fn x => Array.update(arr,x,i::Array.sub(arr,x))) xs)
                                  xs_in_re
                           in Vector.tabulate(max,fn x => rev(Array.sub(arr,x)))
                           end
            val xs_of_re = let val arr = Array.array(Vector.length xreVec,SOME nil)
                               fun addX x re = case Array.sub(arr,re)
                                                 of NONE => ()
                                                  | SOME xs => Array.update(arr,re,SOME(x::xs))
                               fun spoilRe re = Array.update(arr,re,NONE)
                               val _ = app 
                                  (fn (x,rhss) => app 
                                   (fn rhs => 
                                    case rhs 
                                      of FLAT_TEXT _ => ()
                                       | FLAT_ELEM(_,fe) => 
                                            case fe
                                              of nil => ()
                                               | [(true,re)] => addX x re
                                               | _ => app (fn (_,re) => spoilRe re) fe)
                                   rhss)
                                  rules
                               val _ = app 
                                  (fn fe => case fe
                                              of nil => ()
                                               | [(true,re)] => ()
                                               | _ => app (fn (_,re) => spoilRe re) fe) 
                                  starts
                           in Vector.tabulate(Array.length arr,
                                              fn x => Option.map rev (Array.sub(arr,x)))
                           end
         in
            (res_of_x,xs_of_re)
         end

      fun reRightIgnoring berry x =
         let 
            val yXs = Array.foldli 
               (fn (y,(x',_),yXs) => if x=x' then y::yXs else yXs) 
               nil berry
               
            fun follow y = let val (_,(flw,_,_,_)) = Array.sub(berry,y) in flw end
            fun final y = let val (_,(_,_,fin,_)) = Array.sub(berry,y) in fin end

            fun oneStep q = sortInt
               (foldr
                (fn (y,y1s) => foldr
                 (fn ((y1,x),y1s) => if x=xTrue andalso final y1 then y1::y1s else y1s
                  ) y1s (follow y)
                 ) nil q)
               
            fun oneState y =
               if not (final y) then false
               else let val q0 = [y]
                        fun doit (seen,q) = 
                           let val q1 = oneStep q
                           in if not (isEmptyIntList (capIntLists (seen,q1)))
                                 then true
                              else let val new = diffIntLists (q1,seen)
                                   in if isEmptyIntList new then false
                                      else doit(cupIntLists(seen,new),new)
                                   end
                           end
                        in doit (q0,q0)
                    end
                 
            fun allStates nil = true
              | allStates (y::ys) = if oneState y then allStates ys else false
         in 
            allStates yXs
         end

      fun isRightIgnoring (flat as ((max,_,_),xreVec,_,_),targets) =
         let 
	   val (res_of_x,xs_of_re) = computeOccs flat
	   val checked = Array.array(max,false)
	     
	   exception Failed	   
	   	     
	   fun do_wl nil = true
              | do_wl (x::wl) = 
	     if Array.sub(checked,x) then do_wl wl
	     else let 
		    val wl1 = foldr 
		      (fn (re,wl) => 
		       case Vector.sub(xs_of_re,re)
			 of NONE => raise Failed
		       | SOME xs1 => if reRightIgnoring (#2(Vector.sub(xreVec,re))) x
				       then xs1@wl else raise Failed)
		      wl (Vector.sub(res_of_x,x))
		    val _ = Array.update(checked,x,true)
		  in do_wl wl1
		  end
         in 
	   (do_wl targets) handle Failed => false
         end

      fun isAttIgnoring (targets,xXaXcs,xDontCare) =
	 let
	   fun isI targets =
	     List.all
	     (fn (x,xaXcs) =>
	      if IntLists.inIntList (x,targets) then 
		List.all (fn (xAtts,xCont) => xAtts=xDontCare) xaXcs
	      else true)
	     (IntListMap.listItemsi xXaXcs)
	 in
	   isI targets
	 end

      fun isContIgnoring (targets,xXaXcs,xDontCare) =
	 let
	   fun isI targets =
	     List.all
	     (fn (x,xaXcs) =>
	      if IntLists.inIntList (x,targets) then 
		List.all (fn (xAtts,xCont) => xCont=xDontCare) xaXcs
	      else true)
	     (IntListMap.listItemsi xXaXcs)

	 in
	   isI targets
	 end
       
       
      fun matchSpec2Targets (prim,secs) =
	let
	  fun prim2Targets (f,targets) = 
	    IntLists.cupIntLists (targets,Formula.formulaVars f)
	in
	  List.foldl
	  (fn (sec,targets) => IntLists.cupIntLists (targets,prim2Targets sec)) 
	  (prim2Targets prim) secs
	end

      fun analyze (flat as ((_,_,rules),xreVector,_,xXaXcs),
		   matchSpec,xDontCare) = 
	let
	  val targets = matchSpec2Targets matchSpec
	  val single = 
	    if !O_FORCE_SINGLE then true
	    else 
	      if !O_FORCE_DOUBLE then false
	      else isRightIgnoring (flat,targets)
	  val isAttributeIgnoring = isAttIgnoring (targets,xXaXcs,xDontCare)
	  val isContentIgnoring = isContIgnoring (targets,xXaXcs,xDontCare)
	  val pre = 
	    if single then SINGLE (PreAlg.preAlg (flat,matchSpec))
	    else DOUBLE (PreArgBlg.preArgBlg (flat,matchSpec))
	in
	   (isContentIgnoring,pre)
	end

      fun multAnalyze (flat as ((_,_,rules),xreVector,_,xXaXcs),
		       matchSpecs,xDontCare,intervals)=
	let
	  val targets = 
	    List.map matchSpec2Targets matchSpecs
	  val single = 
	    if !O_FORCE_SINGLE then true
	    else 
	      if !O_FORCE_DOUBLE then false
	      else List.all (fn targets => isRightIgnoring (flat,targets)) targets
	  val isContentIgnoring = 
	    List.all (fn targets => isContIgnoring (targets,xXaXcs,xDontCare)) targets
	  val pre = 
	    if single then SINGLE (PreAlg.multPreAlg intervals (flat,matchSpecs))
	    else DOUBLE (PreArgBlg.multPreArgBlg intervals (flat,matchSpecs))
	in
	   (isContentIgnoring,pre)
	end

   end
