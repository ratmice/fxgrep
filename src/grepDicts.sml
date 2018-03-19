functor KeyRegExp ( structure KeyA : Key ) : Key =
   struct
      open RegExp
 
      type Key = KeyA.Key RegExp
         
      val null     = RE_NULL
      val hash     = hashRegExp KeyA.hash
      val compare  = compareRegExp KeyA.compare
      val toString = RegExp2String KeyA.toString
   end

structure KeyX : Key = 
   struct
      type Key = int
      val null = 0
      val hash = Word.fromInt
      val compare = Int.compare
      val toString = Int.toString
   end
structure KeyXRegExp = KeyRegExp ( structure KeyA = KeyX )
structure XRegExpDict = Dict ( structure Key = KeyXRegExp )

structure KeyCharPattern : Key = 
   struct
      open GramData GramUtil GramString

      type Key = CharPattern
      val null = CP_NEG nil
      val hash = hashCharPattern
      val compare = compareCharPattern
      val toString = CharPattern2String
   end
structure KeyTextPattern = KeyRegExp ( structure KeyA = KeyCharPattern )
structure TextPatternDict = Dict ( structure Key = KeyTextPattern )

functor KeyPair ( structure KeyA : Key structure KeyB : Key ) : Key = 
   struct
      type Key = KeyA.Key * KeyB.Key 
      val null = (KeyA.null,KeyB.null)
      val hash = UtilHash.hashPair (KeyA.hash,KeyB.hash)
      val compare = UtilCompare.comparePair (KeyA.compare,KeyB.compare)
      fun toString(a,b) = String.concat ["(",KeyA.toString a,",",KeyB.toString b,")"]
   end
structure KeyIntPair = KeyPair ( structure KeyA = KeyInt structure KeyB = KeyInt )
structure IntPairDict = Dict ( structure Key = KeyIntPair )

functor KeyList ( structure KeyA  : Key ) : Key = 
   struct
      type Key = KeyA.Key list
      val null = nil
      val hash = UtilHash.hashList KeyA.hash
      val compare = UtilCompare.compareList KeyA.compare
      val toString = UtilString.List2String KeyA.toString
   end
structure KeyIntList = KeyList ( structure KeyA = KeyInt )
structure IntListDict = Dict ( structure Key = KeyIntList )

functor KeyPair ( structure KeyA : Key structure KeyB : Key ) : Key = 
   struct
      type Key = KeyA.Key * KeyB.Key 
      val null = (KeyA.null,KeyB.null)
      val hash = UtilHash.hashPair (KeyA.hash,KeyB.hash)
      val compare = UtilCompare.comparePair (KeyA.compare,KeyB.compare)
      fun toString(a,b) = String.concat ["(",KeyA.toString a,",",KeyB.toString b,")"]
   end
structure KeyIntPair = KeyPair ( structure KeyA = KeyInt structure KeyB = KeyInt )
structure IntPairDict = Dict ( structure Key = KeyIntPair )

structure KeyIntIntList = KeyPair ( structure KeyA = KeyInt structure KeyB = KeyIntList )
structure IntIntListDict = Dict ( structure Key = KeyIntIntList )


functor KeyQuad ( structure KeyA : Key ) : Key = 
   struct
      type Key = KeyA.Key * KeyA.Key * KeyA.Key * KeyA.Key 
      val null = (KeyA.null,KeyA.null,KeyA.null,KeyA.null)
      fun hash (a,b,c,d) = 
         0w1327 * KeyA.hash a + 0w3853 * KeyA.hash b + 0w2851 * KeyA.hash c + KeyA.hash d 
      fun compare ((a1,b1,c1,d1),(a2,b2,c2,d2)) = 
         case KeyA.compare(a1,a2)
           of EQUAL => (case KeyA.compare(b1,b2)
                          of EQUAL => (case KeyA.compare(c1,c2)
					  of EQUAL => KeyA.compare(d1,d2)
					   | order => order)
                           | order => order) 
            | order => order 
      fun toString(a,b,c,d) = String.concat 
	 ["(",KeyA.toString a,",",KeyA.toString b,",",KeyA.toString c,",",KeyA.toString d,")"]
   end

functor KeyTriple ( structure KeyA : Key ) : Key = 
   struct
      type Key = KeyA.Key * KeyA.Key * KeyA.Key
      val null = (KeyA.null,KeyA.null,KeyA.null)
      fun hash (a,b,c) = 
         0w1327 * KeyA.hash a + 0w3853 * KeyA.hash b + 0w2851 * KeyA.hash c
      fun compare ((a1,b1,c1),(a2,b2,c2)) = 
         case KeyA.compare(a1,a2)
           of EQUAL => (case KeyA.compare(b1,b2)
                          of EQUAL => KeyA.compare(c1,c2)
			  | order => order)
	 | order => order
      fun toString(a,b,c) = String.concat 
	 ["(",KeyA.toString a,",",KeyA.toString b,",",KeyA.toString c,")"]
   end

structure KeyIntTriple = KeyTriple (structure KeyA = KeyInt)
structure IntTripleDict = Dict (structure Key = KeyIntTriple)
structure KeyIntQuad = KeyQuad ( structure KeyA = KeyInt structure KeyB = KeyInt )
structure IntQuadDict = Dict ( structure Key = KeyIntQuad )
