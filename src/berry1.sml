signature Berry1 =
   sig
      type A
      type Follow  = (int * A) list
      type Berry   = (Follow * bool * bool) array

      val nullBerry : Berry

      val berry : A RegExp1.RegExp -> Berry
   end
structure Berry1 : Berry1 = 
struct
   open 
      RegExp1 UtilError UtilList
      
   val THIS_MODULE = "Berry1"

   type A = GramData.TargetNodePattern
   val null = (GramData.NT_TRUE,[])
   val compareA = GramUtil.compareTargetNodePattern

   fun compareIntA ((i1,a1),(i2,a2)) = 
      case Int.compare(i1,i2) 
	of EQUAL => compareA(a1,a2)
	 | order => order

   type Follow  = (int * A) list
   type Berry   = (Follow * bool * bool) array

   val nullBerry = Array.fromList nil : Berry

   val mergeFst = merge compareIntA
   val mergeLst = merge compareIntA
   val mergeFlw = merge compareIntA
      
   datatype 'a InfoRegExp' = 
       IRE_NULL
     | IRE_EMPTY
     | IRE_BASIC of A
     | IRE_DEEP of A
     | IRE_OPT of 'a InfoRegExp
     | IRE_REP of 'a InfoRegExp
     | IRE_PLUS of 'a InfoRegExp
     | IRE_SEQ of 'a InfoRegExp * 'a InfoRegExp
     | IRE_ALT of 'a InfoRegExp * 'a InfoRegExp
   withtype 'a InfoRegExp = 'a * 'a InfoRegExp'
      
   fun passOne re = 
      let 
	 fun doit n re =
	    case re 
	      of RE_NULL => ((n,false,nil,nil),IRE_NULL)
	       | RE_EMPTY => ((n,true,nil,nil),IRE_EMPTY)
	       | RE_UNDER => raise InternalError 
		 (THIS_MODULE,"passOne","RE_UNDER in regular expression")
	       | RE_BASIC a => ((n+1,false,[(n+1,a)],[(n+1,a)]),IRE_BASIC a)
               | RE_DEEP a => ((n+1,false,[(n+1,a)],[(n+1,a)]),IRE_DEEP a)
	       | RE_OPT re1 => let val ire1 as ((n1,_,fst,lst),_) = doit n re1
			       in ((n1,true,fst,lst),IRE_OPT ire1)
			       end
	       | RE_REP re1 => let val ire1 as ((n1,_,fst,lst),_) = doit n re1
			       in ((n1,true,fst,lst),IRE_REP ire1)
			       end
	       | RE_PLUS re1 => let val ire1 as ((n1,mt,fst,lst),_) = doit n re1
				in ((n1,mt,fst,lst),IRE_PLUS ire1)
				end
	       | RE_SEQ(re1,re2) => let val ire1 as ((n1,mt1,fst1,lst1),_) = doit n re1
					val ire2 as ((n2,mt2,fst2,lst2),_) = doit n1 re2
					val mt = mt1 andalso mt2
					val fst = if mt1 then mergeFst(fst1,fst2) else fst1
					val lst = if mt2 then mergeLst(lst1,lst2) else lst2
				    in ((n2,mt,fst,lst),IRE_SEQ(ire1,ire2))
				    end
	       | RE_ALT(re1,re2) => let val ire1 as ((n1,mt1,fst1,lst1),_) = doit n re1
					val ire2 as ((n2,mt2,fst2,lst2),_) = doit n1 re2
					val mt = mt1 orelse mt2
					val fst = mergeFst(fst1,fst2)
					val lst = mergeLst(lst1,lst2)
				    in ((n2,mt,fst,lst),IRE_ALT(ire1,ire2))
				    end
      in doit 0 re
      end
   
   fun passTwo (ire as ((n,mt,fst,lst),_)) = 
      let 
	 val tab = Array.array(n+1,(nil,false,false))
	 val _ = Array.update(tab,0,(fst,mt,mt))
	    
	 fun doit (ffi as (flw,fin,ini)) ((n,_,fst,lst),re) =
	    case re
	      of IRE_NULL => ()
	       | IRE_EMPTY => ()
	       | IRE_BASIC a => Array.update(tab,n,ffi)
               | IRE_DEEP (_,(pos,_,_)) => 
		Array.update
		(tab,
		 n,
		 ((n,(false,(pos,GramData.NT_GI GramUtil.GI_DOT,nil)))::flw,
		  fin,ini))
	       | IRE_OPT ire1 => doit ffi ire1
	       | IRE_REP ire1 => doit (mergeFlw(fst,flw),fin,ini) ire1
	       | IRE_PLUS ire1 => doit (mergeFlw(fst,flw),fin,ini) ire1
	       | IRE_ALT(ire1,ire2) => (doit ffi ire1; doit ffi ire2)
	       | IRE_SEQ(ire1 as ((_,mt1,_,lst1),_),ire2 as ((_,mt2,fst2,_),_)) => 
		 (doit (if mt2 then mergeFlw(fst2,flw) else fst2,mt2 andalso fin,ini) ire1;
		  doit (flw,fin,mt1 andalso ini) ire2)
		 
	    val _ = doit (nil,true,true) ire
      in tab
      end
   
   fun berry re = passTwo (passOne re)
end

