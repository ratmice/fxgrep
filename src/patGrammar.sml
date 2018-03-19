signature PatGrammar = 
   sig
     val Pattern2Grammar : GramTables.XTable -> GramData.Pattern -> 
       GramData.Grammar * GramData.MatchSpec

     val Patterns2Grammar : 
       (* symbol table *)
       GramTables.XTable -> 

       (* vector of match patterns and corresponding select patterns *)
       (GramData.Pattern * GramData.Pattern list) vector ->  

       GramData.Grammar * GramData.MatchSpec list * (* grammar and targets *)
       (int * int) vector (* intervals = mapping from state to match pattern no *)



   end

structure PatGrammar : PatGrammar =
  struct
    open DocDtd Errors GramData GramTables GramUtil IntLists RegExp
      
    val THIS_MODULE = "PatGrammmar"
      
    fun do_fp pars fp hashFe = 
      case fp
	of RE_NULL => (pars,RE_NULL,false)
      | RE_EMPTY => (pars,RE_EMPTY,false)
      | RE_UNDER => raise InternalError
	  (THIS_MODULE,"do_fp","RE_UNDER encountered")
      | RE_BASIC tp =>
	  if isTP_TRUE tp then (pars,RE_BASIC xTrue,false)
	  else 
	    if isTP_WHITE tp then (pars,RE_BASIC xWhite,false)
	    else 
	      (case tp of
		 TP tp =>
		   let
		     val (next,rules,targets') = pars
		     val ((next1,rules1,(_,targets')),xs) = 
		       do_tp (next,rules,(nil,targets')) tp
		     val res = makeAlt(map RE_BASIC xs)
		   in 
		     ((next1,rules1,targets'),res,false)
		   end
	       | HASH => (pars,hashFe,true))
      | RE_OPT fp1 => 
		 let 
		   val (pars1,xre1,cxtFound) = do_fp pars fp1 hashFe
		 in 
		   (pars1,RE_OPT xre1,cxtFound) 
		 end
      | RE_REP fp1 => 
		 let 
		   val (pars1,xre1,cxtFound) = do_fp pars fp1 hashFe
		 in 
		   (pars1,RE_REP xre1,cxtFound) 
		 end
      | RE_PLUS fp1 => 
		 let 
		   val (pars1,xre1,cxtFound) = do_fp pars fp1 hashFe
		 in 
		   (pars1,RE_PLUS xre1,cxtFound) 
		 end
      | RE_SEQ(fp1,fp2) => 
		 let 
		   val (pars1,xre1,cxtFound1) = do_fp pars fp1 hashFe
		   val (pars2,xre2,cxtFound2) = do_fp pars1 fp2 hashFe
		 in 
		   (pars2,RE_SEQ(xre1,xre2),cxtFound1 orelse cxtFound2)
		 end
      | RE_ALT(fp1,fp2) => 
		 let 
		   val (pars1,xre1,cxtFound1) = do_fp pars fp1 hashFe
		   val (pars2,xre2,cxtFound2) = do_fp pars1 fp2 hashFe
		 in 
		   (pars2,RE_ALT(xre1,xre2),cxtFound1 orelse cxtFound2)
		 end

    (* handle a tree pattern which is not top-level, but occurs
     within some structural or contextual condition *)
    and do_tp pars tp = 
      let 
	val (direct,cp) = tp
	val (pars1,xs) = do_cp pars cp
	val (pars2,xxs) = 
	  if direct then (pars1,xs)
	  else 
	    let 
	      val (next1,rules1,(targets1,targets')) = pars1
	      val (x,next2) = (next1,next1+1)
	      val xxs = addIntList(x,xs)
	      val xre = makeSeq 
		[XRE_UNDER,makeAlt(map RE_BASIC xxs),XRE_UNDER]
	      val ru = [RHS_TREE(TAG_UNDER,[(true,xre)])]
	    in 
	      ((next2,(x,ru)::rules1,(targets1,targets')),xxs)
	    end
      in 
	(pars2,xxs)
      end
    
    and do_ip (next,rules,(targets,targets')) 
      (isSecondaryTarget,pos,rhssLast,structTarget) (* info about the last node *)
      isCxt (sign,incompletePattern) = 
      (* is Cxt means is context for a target; i.e. some top-level
       incomplete path, not from some path from some structural
       constraint for example *)
      let
	val berry = Berry1.berry incompletePattern
	val berryLength = Array.length berry
	  
	val vars = Array.array(berryLength,nil)
	(*reserve for each state a number of variables equal
	 to the outgoing transitions (necessary for binary
	 queries in order to be able to precisely identify the
	 secondary target); a supplementary variable for final
	 states*)
	val next =
	  Array.foldli 
	  (fn (i,state as (follow,isFinal,_),next) =>
	   let
	     val s = List.length follow
	     val (next,l) =
	       if isFinal then
		 (next+s+1,List.tabulate (s+1,fn i =>next+i))
	       else (next+s,List.tabulate (s,fn i =>next+i))
	     val _ = Array.update(vars,i,l)
	   in
	     next
	   end)
	  next
	  (berry,0,NONE)
	  
	val starts = Array.sub (vars,0) (*the variables associated with the start state*)
	(*implies that 0 is always the one and only initial state*)
	  
	val (next,rules,(contextTargets,targets')) =
	  (* for each node in the automaton describing the incomplete path *)
	  Array.foldli
	  (fn (from,
	       (follow,isFinal,_),
	       (pars3 as (next3,rules3,(targets3,targets')))) =>
	   let
	     val xFromVars = Array.sub(vars,from) 
	     (*the variables associated with the current state*)
	       
	     val (xFromVars,next4,rules4,targets') =
	       List.foldl
	       (fn ((to,(* state to which the transition points *)
		     np as (isSecondaryTarget,(pos,_,_))), 
		    (* label of the transition *)
		    (xFromVars,next,rules,targets')) =>
		let
		  (*add a rule for each outgoing transition*)
		  val xToVars = Array.sub(vars,to)
		  val (next,rules,targets',rhss) = 
		    do_transition (next,rules,targets',nil)
		    xToVars np
		  (*consume one of the reserved variables*)
		  val x = List.hd xFromVars
		  val targets' =
		    if isSecondaryTarget then 
		      (true (* a secondary target which does not correspond to the last node can not be negated *)
		       ,pos,x)::targets'
		    else targets'
		  val rules = (x,rhss)::rules
		in
		  (List.tl xFromVars,next,rules,targets')
		end)
	       (xFromVars,next3,rules3,targets')
	       follow
	     val (rules5,targets5,targets') = 
	       case xFromVars of
		 [x] => (*it is a final state, add a rule for
			 the last node, update target variables*)
 
(* one could expect that the rule added for x shouldn't care about the
structure of a match, and have only the wild card _ on the rhs; but
this x could be used to resolve some # in the context => one cannot
use a target with arbitrary structure when generating the context,
because this might spoil the context; in other words, sometimes it
might be that the structure has to be verified in the context too,
this is the case if a # occurs multiple times or in a regular
expression *)
		   ((x,rhssLast)::rules4,
		    if isCxt then x::targets3 else targets3, 
		    if isSecondaryTarget then (sign,pos,x)::targets' else targets')
	       | nil
		   => (rules4,targets3,targets') 
		 | _ => raise InternalError (THIS_MODULE,"do_cp","more than 1 vars for xFrom left")
		     
	   in
	     (next4,rules5,(targets5,targets'))
	   end)
	  (next,rules,(nil,targets'))
	  (berry,0,NONE)

	  
	val targets= 
	  if isCxt then (* we found new targets *)
	    (sign,ListMergeSort.sort Int.> contextTargets)::targets
	  else targets
      (* what we collected are not targets, they
       correspond to some structural/contextual condition *)

      in
	((next,rules,(targets,targets')),starts)
      end

    (* top tree-pattern *)
    and do_ttp (next,rules,(targets,targets')) tp = 
      let 
	val (direct,(ips,lastNode as (isSecondaryTarget,(pos,_,_)))) = tp
	val ((next,rules,targets'),rhssLast) = 
	  do_lastNodeRhss (next,rules,targets') lastNode
	  
	(* the structure rules - added when the last node is not
	 the only node in the pattern *)
	val (next,rules,starts,structTarget) =
	  if ips<>nil then 
	    (* add rules to find the last node at an arbitrary depth *)
	    let
	      val x1 = next
	      val x2 = next+1
	      val fe = [(true,makeSeq [XRE_UNDER,
				       makeAlt [RE_BASIC x1,RE_BASIC x2],
					   XRE_UNDER])]
	      val rhs = RHS_TREE ((GI_UNDER,nil),fe)
	      val rule1 = (x1,[rhs])
	      val rule2 = (x2,rhssLast)
	    in
	      (next+2,[rule2,rule1]@rules,[x1,x2],SOME x2)
	    end
	  else (* we have a single node *)
	    (next+1,(next,rhssLast)::rules,[next],SOME next)
	    
	val targets = targets@[(true,[Option.valOf structTarget])]
	  
	val (pars1,xs) = 
	  (* for each incomplete pattern *)
(* one could treat specially the case of just one ip in order not to duplicate the rules for the structure *)
	  List.foldl 
	  (fn ((sign,(direct,ip)),((next,rules,(targets,targets')),starts)) =>
	   let
	     (* add rules and update targets *)
	     val ((next1,rules1,(targets1,targets1')),starts1) =
	       do_ip (next,rules,(targets,targets')) 
	       (isSecondaryTarget,pos,rhssLast,structTarget) 
	       true (* is a top-level incomplete pattern *)
	       (sign,ip)
	       
	     (* posibly add rule to match the pattern at some arbitrary depth *)
	     val (next2,rules2,starts2) = 
	       if direct then (next1,rules1,starts@starts1)
	       else
		 let
		   val (x,next) = (next1,next1+1)
		   val starts1 = starts1@[x]
		   val xre = makeSeq 
		     [XRE_UNDER,makeAlt(map RE_BASIC starts1),XRE_UNDER]
		   val ru = [RHS_TREE(TAG_UNDER,[(true,xre)])]
		 in 
		   (next,(x,ru)::rules1,starts@starts1)
		 end
	   in
	     ((next2,rules2,(targets1,targets1')),starts2)
	   end) ((next,rules,(targets,targets')),starts) ips

	    val (pars2,xxs) = 
	      if direct then (pars1,xs)
	      else   (* could be optimized *)
		let 
		  val (next1,rules1,(targets1,targets')) = pars1
		  val (x,next2) = (next1,next1+1)
		  val xxs = addIntList(x,xs)
		  val xre = makeSeq 
		    [XRE_UNDER,makeAlt(map RE_BASIC xxs),XRE_UNDER]
		  val ru = [RHS_TREE(TAG_UNDER,[(true,xre)])]
		in 
		  ((next2,(x,ru)::rules1,(targets1,targets')),xxs)
		end
	  in 
	    (pars2,xxs)
	  end
	
	(* some complete pattern in some structural/contextual condition *)
	and do_cp (pars as (next,rules,(targets,targets'))) cp =
	  case cp of
	    CP_NODE node => 
	      do_single_node pars node
	  | CP_COMPOSED (incompletePattern,
			 lastNode as (isSecondaryTarget,(pos,_,_))) =>
	      let
		val ((next,rules,targets'),rhssLast) = 
		  do_lastNodeRhss (next,rules,targets') lastNode
		val ((next1,rules1,(targets1,targets1')),starts) =
		  do_ip (next,rules,(targets,targets')) 
		  (isSecondaryTarget,pos,rhssLast,NONE(*structTarget*)) 
		  false (* is not a top-level incomplete pattern *)
		  (true, (* not-negated ip; negation are allowed only for top-level ips *)
		   incompletePattern)
	      in
		((next1,rules1,(targets1,targets1')),starts)
	      end
	  | CP_OR (cp1,cp2) =>
	      let
		val (pars1,xs1) = do_cp pars cp1
		val (pars2,xs2) = do_cp pars1 cp2
	      in
		(pars2,cupIntLists(xs1,xs2))
	      end

	and do_transition (next,rules,targets',rhss) xToVars 
	  (np as (_,(_,nt,qs))) =
	  case nt of
	    NT_TEXT _ => (next,rules,targets',rhss)
	  | NT_GI gp => do_elem (next,rules,targets',rhss) xToVars (gp,false,qs)
	  | NT_TRUE => do_elem (next,rules,targets',rhss) xToVars (GI_UNDER,true,qs)
	  | NT_PI target => do_pi_rhss (next,rules,targets',rhss) xToVars (target,qs)

	and do_pi_rhss (next,rules,targets',rhss) xToVars (target,qs) = 
	  let 
	    val hashFe = makeAlt (map RE_BASIC xToVars)
	    val ((next1,rules1,targets'),aps,feContent,cxtFound) = 
	      do_qs (next,rules,targets') hashFe qs
	    val _ = if null aps then () else raise InternalError
	      (THIS_MODULE,"do_pi_rhss","NT_PI with att qualifier")

	    val fe =
	      if cxtFound then feContent
	      else ((true,
		     makeSeq [XRE_UNDER,hashFe,XRE_UNDER])::feContent)

	    val rhss1 = (RHS_PI(target,fe))::rhss
	  in 
	    (next1,rules1,targets',rhss1)
	  end

	and do_elem (next,rules,targets',rhss) xToVars (gp,isTrue,qs) = 
	  let
	    val hashFe = makeAlt(map RE_BASIC xToVars)
	    val ((next2,rules2,targets'),aps,feContent,cxtFound) = 
	      do_qs (next,rules,targets') hashFe qs
	    val fe = 
	      if cxtFound then feContent
	      else
		(true, 
		 makeSeq [XRE_UNDER,
			  makeAlt (map RE_BASIC xToVars),
			  XRE_UNDER])::feContent
	    val rhss = (RHS_TREE((gp,aps),fe))::rhss
	    val rhss = if isTrue andalso not (List.exists #1 feContent orelse 
					      cxtFound)
			 then RHS_TEXT TXT_UNDER::rhss 
		       else rhss
	    val rhss = if isTrue andalso not (List.exists #1 aps)
		       then RHS_PI(TXT_UNDER,fe)::rhss else rhss
	  in
	    (next2,rules2,targets',rhss)
	  end


	and do_lastNodeRhss (next,rules,targets') (_,(_,nt,qs)) =
	  case nt of 
	    NT_TEXT tp => 
	      let 
		val ruText = [RHS_TEXT tp]
	      in 
		((next,rules,targets'),ruText)
	      end
	  | NT_TRUE => 
	      do_lastElemRhss (next,rules,targets') (GI_UNDER,true,qs)
	  | NT_GI gp => 
	      do_lastElemRhss (next,rules,targets') (gp,false,qs)
	  | NT_PI tp => 
	      do_lastPiRhss (next,rules,targets') (tp,qs)

	and do_lastElemRhss (next,rules,targets') (gp,isTrue,qs) = 
	  let 
	    val hashFe = RE_BASIC xTrue
	    val ((next2,rules2,targets'),aps,feContent,cxtFound) = 
	      do_qs (next,rules,targets') hashFe qs
	    val fe = 
	      if feContent = nil then [(true,XRE_UNDER)]
	      else feContent
	    val ru = [RHS_TREE((gp,aps),fe)]
	    val ru = if isTrue andalso not (List.exists #1 feContent orelse
					    cxtFound)
		       then RHS_TEXT TXT_UNDER::ru else ru
	    val ru = if isTrue andalso not (List.exists #1 aps)
		       then RHS_PI(TXT_UNDER,fe)::ru else ru

	  in 
	    ((next2,rules2,targets'),ru)
	  end

	and do_lastPiRhss (next,rules,targets') (target,qs) = 
	  let 
	    val hashFe = RE_BASIC xTrue
	    val ((next1,rules1,targets'),aps,feContent,_) = 
	      do_qs (next,rules,targets') hashFe qs
	    val _ = if null aps then () else raise InternalError
	      (THIS_MODULE,"do_lastPiRhss","NT_PI with att qualifier")

	    val fe = 
	      if feContent = nil then [(true,XRE_UNDER)] else feContent

	    val ru = [RHS_PI(target,fe)]
	  in ((next1,rules1,targets'),ru)
	  end
	    

	and do_single_node (pars as (next,rules,(targets,targets')))
	  (isSecondaryTarget,(pos,nt,qs)) =
	  case nt
	    of NT_TEXT tp => 
	      let 
		val (x,next1) = (next,next+1)
		val targets1 = targets
		val targets1' = 
		  if isSecondaryTarget then (true,pos,x)::targets'
		  else targets'
		val ruText = [RHS_TEXT tp]
	      in ((next1,(x,ruText)::rules,(targets1,targets')),[x])
	      end
	  | NT_TRUE => do_single_elem pars (GI_UNDER,true,qs) (pos,isSecondaryTarget)
	  | NT_GI gp => do_single_elem pars (gp,false,qs) (pos,isSecondaryTarget)
	  | NT_PI tp => do_pi pars (tp,qs) (pos,isSecondaryTarget)

	and do_single_elem (pars as (next,rules,(targets,targets'))) 
	  (gp,isTrue,qs) (pos,isSecondaryTarget) = 
	  let 
	    val hashFe = RE_BASIC xTrue
	    val ((next1,rules1,targets'),aps,feContent,cxtFound) = 
	      do_qs (next,rules,targets') hashFe qs
	    val fe = 
	      if feContent = nil then 
		(*no structural, no contextual qualifier*)
		[(true,XRE_UNDER)]
	      else feContent
	    val (x,next3) = (next1,next1+1)
	    val ru = [RHS_TREE((gp,aps),fe)]
	    val ru = if isTrue andalso not (List.exists #1 feContent orelse cxtFound)
		       then RHS_TEXT TXT_UNDER::ru else ru
	    val ru = if isTrue andalso not (List.exists #1 aps)
		       then RHS_PI(TXT_UNDER,fe)::ru else ru
	    val targets' = 
	      if isSecondaryTarget then (true,pos,x)::targets'
	      else targets'
	  in ((next3,(x,ru)::rules1,(targets,targets')),[x])
	  end

	and do_pi (pars as (next,rules,(targets,targets'))) (target,qs) (pos,isSecondaryTarget) = 
	  let 
	    val hashFe = RE_BASIC xTrue
	    val ((next1,rules1,targets'),aps,feContent,_) = do_qs (next,rules,targets') hashFe qs
	    val _ = if null aps then () else raise InternalError
	      (THIS_MODULE,"do_pi","NT_PI with att qualifier")

	    val fe = 
	      if feContent = nil then [(true,XRE_UNDER)] else feContent

	    val (x,next2) = (next1,next1+1)
	    val ru = [RHS_PI(target,fe)]
	    val targets' = if isSecondaryTarget then (true,pos,x)::targets'
			   else targets'
	  in ((next2,(x,ru)::rules1,(targets,targets')),[x])
	  end

	(* handle normal qualifiers *)
	and do_qs pars hashFe qs = foldr 
	  (fn ((sign,q),(pars,aps,feCont,cxtFound)) 
	   => case q of 
	   Q_CHILDREN fp => 
	     let 
	       val (pars1,xre,cxtFound1) = do_fp pars fp hashFe
	     in 
	       (pars1,aps,(sign,xre)::feCont,cxtFound orelse cxtFound1)
	     end
	 | Q_ATT ap => (pars,(sign,ap)::aps,feCont,cxtFound))
	  (pars,nil,nil,false) qs
             
	(* handle pattern qualifiers *)
	fun do_pqs hashFe pars qs = foldr 
	  (fn ((sign,fp),(pars,fe,cxtFound)) 
	   => let 
		val (pars1,xre,cxtFound1) = do_fp pars fp hashFe
	      in 
		(pars1,(sign,xre)::fe,cxtFound orelse cxtFound1)
	      end)
	  (pars,nil,false) qs

	fun do_pat (pars as (next,rules,(targets,targets'))) (pqs,ttp(*top-level tree pattern*)) =
	  let 
	    val ((next1,rules1,(targets1,targets')),xs) = 
	      do_ttp (next,rules,(targets,targets')) ttp
	    val hashFe = makeAlt(map RE_BASIC xs)
	    val ((next2,rules2,targets'),fePqs,cxtFound) = 
	      do_pqs hashFe (next1,rules1,targets') pqs
	    val fe = 
	      if cxtFound then 
		(* a hash was found => the start variables have been
		put in the required context *)
		fePqs
	      else
		let
		  val re = 
		    RE_SEQ(XRE_UNDER,
			   RE_SEQ((makeAlt (map RE_BASIC xs)),
				  XRE_UNDER))
		in
		  (true,re)::fePqs 
		end

	      (* when removing dynamic selects we are only interested
	      in the start variables, i.e. hashFe *)

	  in 
	    ((next2,rules2,(targets1,targets')),(fe,hashFe))
	  end

	fun doTargets' targets' =
	  let
	    (* sort the secondary targets accordingly to the position
	    of the corresponding node in pattern *)
	    val targets' = 
	      (ListMergeSort.sort
	       (fn ((_,(_,l1,c1),_),(_,(_,l2,c2),_)) =>
		(l1>l2) orelse ((l1=l2) andalso (c1>c2))) targets')

	    (* group together targets which have the same position, as
	    belonging to the same secondary order *)
	    val (pos,secOrdTargets,targets') =
	      List.foldl
	      (fn ((sign,(s1,l1,c1),target),((s2,l2,c2),secOrdTargets,targets)) =>
	       if l1=l2 andalso c1=c2 then
		 ((s1,l1,c1),(sign,target)::secOrdTargets,targets)
	       else if secOrdTargets <> nil then
		 ((s1,l1,c1),[(sign,target)],(List.rev secOrdTargets)::targets)
		    else ((s1,l1,c1),[(sign,target)],targets))
	      (nullPosition,nil,nil) targets'
	    val targets' = 
	      if secOrdTargets <> nil then
		List.rev ((List.rev secOrdTargets)::targets')
	      else List.rev targets'

	    (* in case of secondaries specified via patterns there is
	    no conjunction of targets and all targets are positive,
	    except when the secondary target is the same as the last
	    target and is the last node following an incomplete path;
	    *)
	    val targets' =
	      List.map
	      (fn targets => (* for the targets corresponding to each secondary order *)
	       let
		 (* collect the negated and the positive targets *)
		 val (neg,pos) =
		   List.foldl 
		   (fn ((sign,x),(neg,pos)) =>
		    if sign then (neg,x::pos)
		    else (x::neg,pos))
		   (nil,nil) targets
	       in
		 (* all positive targets belong together *)
		 [(true,
		   (* within a secondary order targets' must be ordered *)
		   ListMergeSort.sort Int.> pos )
		  ]
		 @ (* every negated target is alone *)
		 (List.map (fn n => (false,[n])) neg)
	       end)
	      targets'
	  in
	    targets'
	  end

	fun makeAltVar vars =
	  List.foldl 
	  (fn (x,f) => Formula.OR (Formula.VAR x,f)) 
	  (Formula.VAR (hd vars)) (tl vars)

	fun makePatForm targets1 =
	  List.foldl	  
	  (fn ((sign,targets),f) => 
	   let
	     val f1 = makeAltVar targets
	   in
	     if sign then Formula.AND (f1,f)
	     else Formula.AND (Formula.NOT f1,f)
	   end)	  
	  (let
	     val (sign,targets) = hd targets1
	     val f = makeAltVar targets
	   in
	     if sign then f else Formula.NOT f
	   end)	     
	     (tl targets1)

	fun makePat (next,pats) =
	  List.foldl 
	  (fn (pat,(pars as (next,rules,(targets,targets')),fes,f)) => 
	   let 
	     val ((next2,rules2,(targets1,targets2')),(fe,startAlt)) = 
	       do_pat (next,rules,(nil,targets')) pat
	     val f1 = makePatForm targets1
	   in 
	     ((next2,rules2,(targets1,targets2')),fe::fes,Formula.OR (f1,f))
	   end)
	  (let
	     val ((next,rules,(targets,targets')),(fe,startAlt))= do_pat (next,nil,(nil,nil)) (hd pats)
	     val f = makePatForm targets
	   in
	     ((next,rules,(targets,targets')),[fe],f)
	   end) (tl pats)

	(* do one match pattern *)
	fun do_one (first,pats) = 
	  let 
	    val ((next,rules,(targets,targets')),starts,f) = makePat (first,pats)
	    val targets' = doTargets' targets'
	    val targets  = sortInt (List.foldl (fn ((_,t),xs) => xs@t) nil targets)
	    val targets' = List.map 
	      (fn targets =>sortInt (List.foldl (fn ((_,t),xs) => xs@t) nil targets))
	      targets'
	  in 
	    (next,rules,starts,(f,(targets,targets')))
	  end	

	fun Pattern2Grammar tab pats =
	  let 
            val (next,rules) = extractXTable tab
	    val (max,newRules,starts,(f,(targets,targets'))) = do_one (next,pats)
	    val secs = List.map (fn targets => (makeAltVar targets,targets)) targets'
            val newRules = rules@rev newRules
	  in 
	    ((max,starts,newRules),((f,targets),secs))
	  end

	fun Patterns2Grammar tab pats =
	   let
            val (first,rules) = extractXTable tab

            val (max,r,targets,s,y) = 
	      (* for each match pattern *)
	      Vector.foldl
	      (fn ((pat,selectPatterns),(first,r,ftt',s,y)) => 
	       let 
		 val (next,rules,starts,(f,(targets,targets'))) = 
		   do_one (first,pat)
		 val targets' = List.map (fn targets => (makeAltVar targets,targets)) targets'
	       in 
		 if selectPatterns = nil then 
		   (next,rules::r,((f,targets),targets')::ftt',starts::s,(first,next-1)::y)
		 else
		   let
		     val (next,startExps,selectRules,targets') = 
		       (* for each selectPattern *)
		       List.foldl
		       (fn (selectPattern,(next,startExps,
					   selectRules,targets')) =>
			let
			  (* translate the select pattern *)
			  val (next,selectRules1,selectStarts1,
			       (selectF,(selectTargets1,selectTargets')))
(* list of forest expressions ; each forest expression is a list of
possibly negated regular expression over x variables, and represents a
alternative pattern in the selectPattern (which is a disjunction of
patterns) *)
			    = do_one (next,selectPattern) 
			    
			in
			  (next,startExps@selectStarts1,
			   selectRules@selectRules1,
 			   targets'@[(selectF,selectTargets1)] 
(* the primary targets of the select patterns get secondary targets 
for the rewritten match pattern *)
			   )
			end) (next,nil,nil,targets')
		       selectPatterns
		     
		     val rules = 
		       (* transform the rules of the match pattern *)
		       List.map
		       (fn (x,rhss) =>
			if IntLists.inIntList (x,(*positiveT*)targets) then 
(* for each rule whose lhs is a primary target variable, for each
select pattern, for each select start expression add a rule whose rhs
(the structural constraint on children) is the original constraint in
conjunction with the start expression; (conjunction is needed to
ensure that the structure of the original target is still fulfilled by
the new rules) *)
			  (x,
			   List.concat
			   (
			    List.map
			    (fn rhs =>
			     case rhs of
			       RHS_TEXT x => [rhs]
			     | RHS_PI (tp,fe) =>
				 rhs::(List.map (fn se => RHS_PI (tp,fe@se)) startExps)
			     | RHS_TREE (taP,fe) =>
				 rhs::(List.map (fn se => RHS_TREE (taP,fe@se)) startExps)
				 
				 )
			    rhss
			    )
			   )
			else (x,rhss)) rules
		     val rules = selectRules@rules
		   in 
		     (next,rules::r,((f,targets),targets')::ftt',
		      starts::s,(first,next-1)::y)
		   end
	       end) (first,nil,nil,nil,nil) pats

            val rules = rules@(List.concat r)
	    (* order of rules is not important; there is one rule per
	    x with one ore more rhss *)

	    val targets = List.rev targets
            val starts  = rev (List.concat s)
            val intervals = Vector.fromList (rev y)
	  in 
	    ((max,starts,rules),targets,intervals)
	  end


   end
