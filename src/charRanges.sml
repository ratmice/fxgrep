signature CharRanges = 
   sig
      eqtype CharRange

      val hashCharRange     : CharRange -> word
      val compareCharRange  : CharRange * CharRange -> order

      val emptyCharRange    : CharRange
      val singleCharRange   : UniChar.Char -> CharRange
      val intervalCharRange : UniChar.Char * UniChar.Char -> CharRange
	 
      val mergeCharRanges   : CharRange * CharRange -> CharRange 
      val diffCharRanges    : CharRange * CharRange -> CharRange 
      val normCharRange     : CharRange -> CharRange 

      val Data2CharRange    : UniChar.Data -> CharRange
      val CharRange2xString : string * string * string * string -> CharRange -> string
   end

structure CharRanges : CharRanges = 
   struct
      open UniChar UtilCompare UtilHash UtilString

      type CharInterval = Char * Char
      type CharRange = CharInterval list

      val emptyCharRange = []
      fun singleCharRange c = [(c,c)]
      fun intervalCharRange lh = [lh]

      val hashCharRange = hashList (hashPair (hashChar,hashChar))
      val compareCharRange = compareList (comparePair (compareChar,compareChar))

      fun mergeCharRanges cr12 = 
	 let fun doit(nil,cr) = cr
	       | doit(cr,nil) = cr
	       | doit(all1 as (lh1 as (l1,h1))::cr1,all2 as (lh2 as (l2,h2))::cr2) = 
	    if h1+0w1<l2 then lh1::doit(cr1,all2)
	    else if h2+0w1<l1 then lh2::doit(all1,cr2)
	    else if h1>h2 then doit((Chars.min(l1,l2),h1)::cr1,cr2)
		 else doit(cr1,(Chars.min(l1,l2),h2)::cr2)
	 in doit cr12
	 end

      fun diffCharRanges cr12 = 
	 let fun doit(nil,cr:CharRange) = nil
	       | doit(cr,nil) = cr
	       | doit(all1 as (lh1 as (l1,h1))::cr1,all2 as (lh2 as (l2,h2))::cr2) = 
	    if h1<l2 then lh1::doit(cr1,all2)
	    else if h2<l1 then doit(all1,cr2)
	    else if l1>=l2 andalso h1<=h2 then doit(cr1,all2)
	    else if l1<l2 then if h1>h2 then (l1,l2-0w1)::doit((h2+0w1,h1)::cr1,cr2)
			       else (l1,l2-0w1)::doit(cr1,cr2)
		 else doit((h2+0w1,h1)::cr1,cr2)
	 in doit cr12
	 end

      fun normCharRange cr =
	 let 
	    fun doit nil = nil
	      | doit [lh] = [lh]
	      | doit ((lh1 as (l1,h1))::(lh2 as (l2,h2))::lhs) =
	       if h1+0w1<l2 then lh1::doit(lh2::lhs)
	       else doit((Chars.min(l1,l2),Chars.max(h1,h2))::lhs)
	 in doit cr
	 end

      fun Data2CharRange cs = foldr 
	 (fn (c,yet) => mergeCharRanges(singleCharRange c,yet)) emptyCharRange cs

      fun CharRange2xString (pre,sep,dash,post) = 
	 List2xString (pre,sep,post) 
	 (fn (l,h) => if l=h then Char2String l 
		      else Char2String l^dash^Char2String h)
   end