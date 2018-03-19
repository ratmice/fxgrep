signature TextDfa =
   sig
      datatype Segment = TRANS of int array | FIXED of int
      type Row = (UniChar.Char * UniChar.Char * Segment) list * int * bool
      type Dfa = Row vector

      type State = int

      val nullDfa : Dfa
      val makeDfa : GramData.TextPattern -> Dfa

      val textStart  : State
      val isFinal    : Dfa * State -> bool
      val transition : Dfa * State * UniChar.Char -> State

      val runDfas    : (int * Dfa) list -> UniChar.Vector -> int list
   end

structure TextDfa : TextDfa =
   struct
      open UniChar IntSets IntSetDict GramData UtilError UtilList

      val textStart = 0
      type State = int
      type StateSet = IntSet
      val addState = addIntSet
      val mergeStates = cupIntSets

      type 'a Transitions = (Char * Char * 'a) list * 'a
      val nullTransitions = (nil,emptyIntSet) : StateSet Transitions
      fun transBounds ((lhs,_) : 'a Transitions) = 
	 if null lhs then (0w1,0w0) else (#1(hd lhs),#2(List.last lhs))

      datatype Segment = TRANS of int array | FIXED of int
      type Row = (Char * Char * Segment) list * int * bool
      type Dfa = Row vector
      val nullSegment = FIXED 0
      val nullRow = (nil,0,false)
      val nullDfa = Vector.fromList []:Dfa

      val SEG_SIZE = 0w256 : Char
      fun transSplit lhqs = 
	 case lhqs
	   of nil => NONE
	    | (lhq as (l,h,_))::rest => 
	      let val thisSize = h-l+0w1
	      in if thisSize>SEG_SIZE
		    then SOME(l,h,[lhq],rest)
		 else let val max = l+SEG_SIZE
			  fun doit hi nil = (hi,nil,nil)
			    | doit hi (all as (lhq as (_,h,_))::rest) = 
			     if h>=max then (hi,nil,all)
			     else let val (hi1,lhqs1,lhqs2) = doit h rest
				  in (hi1,lhq::lhqs1,lhqs2)
				  end
			  val (hi,lhqs1,lhqs2) = doit h rest
		      in SOME(l,hi,lhq::lhqs1,lhqs2)
		      end
	      end
      fun makeSegments (lhqs,def) =
	 case transSplit lhqs
	   of NONE => nil
	    | SOME(lo,hi,lhqs1,rest) => 
	      case lhqs1 
		of [(l,h,q)] => (l,h-l,FIXED q)::makeSegments(rest,def)
		 | _ => let val size = hi-lo
			    val arr = Array.array(Chars.toInt size+1,def)
			    val _ = app
			       (fn (l,h,q) => 
				ArraySlice.modifyi (fn _ => q)
				        (ArraySlice.slice (arr,
					  Chars.toInt(l-lo),
					  SOME(Chars.toInt(h-l+0w1)))))
			       lhqs1
			in (lo,size,TRANS arr)::makeSegments(rest,def)
			end
      fun makeRow NONE = nullRow
	| makeRow (SOME((trans,def),fin)) = (makeSegments(trans,def),def,fin)

      val printQdict = printDict
	 (fn NONE => "NONE"
	   | SOME((lhis,def),fin) => String.concat
	  ["Transitions: ",UtilString.List2xString ("","; ","; ") 
	   (fn (l,h,i) => Char2String l^"-"^Char2String h^"->"^Int.toString i) lhis,
	   "_->",Int.toString def,". Final: ",if fin then "yes" else "no","."])

      fun addPositive((lhs,default),cr,q) =
	 let 
	    val s2 = addState(q,default)
	    
	    fun doit (all1,nil) = all1
	      | doit (nil,all2) = map (fn (l2,h2) => (l2,h2,s2)) all2
	      | doit (all1 as (lhs1 as (l1,h1,s1))::rest1,all2 as (l2,h2)::rest2) = 
	       case compareChar (l1,l2) 
		 of LESS => if h1<l2 then lhs1::doit(rest1,all2)
			    else let val first = (l1,l2-0w1,s1)
				 in first::doit((l2,h1,s1)::rest1,all2)
				 end
		  | EQUAL => let val s12 = addState(q,s1)
				 val (h12,rest12) =
				    case compareChar(h1,h2)
				      of LESS => (h1,(rest1,(h1+0w1,h2)::rest2))
				       | EQUAL => (h1,(rest1,rest2))
				       | GREATER => (h2,((h2+0w1,h1,s1)::rest1,rest2))
				 val first = (l1,h12,s12)
			     in first::doit rest12
			     end
		  | GREATER => if h2<l1 then (l2,h2,s2)::doit(all1,rest2)
			       else let val first = (l2,l1-0w1,s2)
				    in first::doit(all1,(l1,h2)::rest2)
				    end 
	 in (doit(lhs,cr),default)
	 end

      fun addNegative((lhs,default),cr,q) =
	 let 
	    val newDefault = addState(q,default)
	    
	    fun doit (all1,nil) = map (fn (l1,h1,s1) => (l1,h1,addState(q,s1))) all1
              | doit (nil,all2) = map (fn (l2,h2) => (l2,h2,default)) all2
	      | doit (all1 as (lhs1 as (l1,h1,s1))::rest1,all2 as (l2,h2)::rest2) = 
	       case compareChar (l1,l2) 
		 of LESS => if h1<l2 then (l1,h1,addState(q,s1))::doit(rest1,all2)
			    else let val first = (l1,l2-0w1,addState(q,s1))
				 in first::doit((l2,h1,s1)::rest1,all2)
				 end
		  | EQUAL => let val (h12,rest12) =
				 case compareChar(h1,h2)
				   of LESS => (h1,(rest1,(h1+0w1,h2)::rest2))
				    | EQUAL => (h1,(rest1,rest2))
				    | GREATER => (h2,((h2+0w1,h1,s1)::rest1,rest2))
				 val first = (l1,h12,s1)
			     in first::doit rest12
			     end
		  | GREATER => if h2<l1 then (l2,h2,default)::doit(all1,rest2)
			       else let val first = (l2,l1-0w1,default)
				    in first::doit(all1,(l1,h2)::rest2)
				    end 
	 in (doit(lhs,cr),newDefault)
	 end

      fun makeDfa re =
	 let
	    val glushTab = BerryTp.berry re
	    fun isFinal i = #3(#2(Array.sub(glushTab,i)))
	    val qDict = nullDict("text dfa state set",NONE)
	       
	    fun doState(i,q) = 
	       case getByIndex(qDict,i)
		 of SOME _ => ()
		  | NONE => 
		    let
		       val ((lhqs,def),fin) = foldr
			  (fn (j,(trans,fin)) 
			   => let val (_,(flwJ,_,finJ,_)) = Array.sub(glushTab,j)
			      in foldr (fn ((k,cp),(trans,fin)) 
					=> case cp
					     of CP_START => (trans,fin)
					      | CP_END => (trans,fin orelse isFinal k)
					      | CP_POS cr => (addPositive(trans,cr,k),fin)
					      | CP_NEG cr => (addNegative(trans,cr,k),fin))
				 (trans,fin orelse finJ) flwJ
			      end)
			  (nullTransitions,false) (IntSet2List q)
		       val (iqs,lhis) = foldr 
			  (fn ((l,h,q),(iqs,lhis)) 
			   => let val i = getIndex(qDict,q)
			      in ((i,q)::iqs,(l,h,i)::lhis)
			      end) 
			  (nil,nil) lhqs
		       val iDef = getIndex(qDict,def)
		       val _ = setByIndex(qDict,i,SOME((lhis,iDef),fin))
		    in 
		       app doState ((iDef,def)::iqs)
		    end

	    val (_,(flw0,_,fin0,_)) = Array.sub(glushTab,0)
	    val q0 = IntList2Set (0::List.mapPartial (fn (i,CP_START) => SOME i | _ => NONE) flw0)
	    val _ = if getIndex(qDict,q0)=textStart then () 
		    else raise InternalError ("TextDfa","makeDfa","q0's index is different from 0")
	    val _ = doState(textStart,q0)

	    val tab = Vector.tabulate (usedIndices qDict,fn i => makeRow(getByIndex(qDict,i)))
	 in 
	    tab
	 end

      fun isFinal(tab:Dfa,q) = #3(Vector.sub(tab,q))
      fun transition(tab:Dfa,q,c) = 
	 let 
	    val (seg,def,_) = Vector.sub(tab,q)
	    fun doit nil = def 
              | doit ((off,max,this)::rest) =
               if c-off<=max 
                  then case this 
                         of FIXED q1 => q1
                          | TRANS arr => Array.sub(arr,Chars.toInt(c-off))
               else if c<off then def
                    else doit rest 
	 in doit seg
	 end

      fun runDfas iTabs txt =
	 case iTabs 
	   of nil => nil
	    | [(i,tab)] => let val txtLen = Vector.length txt
                               fun doit (j,q) = 
                                  if j>=txtLen then q
                                  else let val c = Vector.sub(txt,j)
                                           val q1 = transition(tab,q,c) 
                                       in doit(j+1,q1)
                                       end 
                               val qF = doit (0,textStart)
                           in if isFinal(tab,qF) then [i] else nil
                           end
	    | _ => let val iTabs = Vector.fromList iTabs
                       val qv0 = Vector.map (fn _ => textStart) iTabs
		       val txtLen = Vector.length txt
		       fun doit (j,qv) = 
			  if j>=txtLen then qv
			  else let val c = Vector.sub(txt,j)
				   val qv1 = Vector.mapi
				      (fn (k,(_,tab)) => transition
				       (tab,Vector.sub(qv,k),c)) 
				      iTabs
			  in doit(j+1,qv1)
			       end 
		       val qvF = doit (0,qv0)
		       val accept = Vector.foldri
			  (fn (k,(i,tab),accept) => 
			   if isFinal(tab,Vector.sub(qvF,k))
			      then i::accept else accept)
			  nil iTabs
		   in accept
		   end
   end
