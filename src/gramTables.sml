signature GramTables =
   sig
      type XTable  

      val tab_ : XTable ref
      val initXTable : unit -> XTable
         
      val X2Index : XTable -> UniChar.Vector -> int
      val Index2X : XTable -> int -> UniChar.Vector

      val declareX: XTable -> UniChar.Vector -> int
      val defineX : XTable -> int * GramData.Rhs -> unit
      val useX    : XTable -> Errors.Position * UniChar.Data -> int
      val getRefs : XTable -> int -> Errors.Position list

      val xTrue   : int
      val xWhite  : int

      val xTrueName  : UniChar.Vector
      val xWhiteName : UniChar.Vector

      val XRE_UNDER : GramData.XRegExp
      val XRE_WHITE : GramData.XRegExp

      val extractXTable : XTable -> int * (int * GramData.Rhs list) list

      val X2xString : XTable -> int -> string
      val X2String  : int -> string
   end

structure GramTables : GramTables =
   struct
      open 
         Errors UniChar VectorDict 
         GramData GramOptions GramUtil

      type XInfo = Rhs list * Errors.Position list
      val nullXInfo = (nil,nil) : XInfo

      type XTable = XInfo Dict

      fun X2Index tab v = getIndex(tab,v)
      fun Index2X tab i = getKey(tab,i)
      fun getRefs tab i = #2(getByIndex(tab,i):XInfo)

      val usedTreeVars = usedIndices 

      fun declareX tab cv = getIndex(tab,cv)
      fun defineX tab (idx,rhs) =
         let 
            val (rhss,refs) = getByIndex(tab,idx)
            val _ = setByIndex(tab,idx,(rhss@[rhs],refs))
         in ()
         end
      fun useX tab (pp,cs) = 
         let 
            val cv = Data2Vector cs
            val idx = getIndex(tab,cv)
            val (rhss,refs) = getByIndex(tab,idx)
            val _ = setByIndex(tab,idx,(rhss,refs@[pp]))
         in 
            idx
         end

      val xTrueName = String2Vector "."
      val xWhiteName = String2Vector "~"

      val tab_ = ref (nullDict("tree variable",nullXInfo))

      fun makeXTable() = 
         let 
            val tab = makeDict("tree variable",!O_TS_TREEVAR,nullXInfo) : XTable
            val xTrue = declareX tab xTrueName 
            val xWhite = declareX tab xWhiteName 
            val _ = defineX tab (xTrue,RHS_TEXT TXT_UNDER)
            val _ = defineX tab (xTrue,RHS_PI(TXT_UNDER,[(true,RE_REP(RE_BASIC xTrue))]))
            val _ = defineX tab (xTrue,RHS_TREE(TAG_UNDER,[(true,RE_REP(RE_BASIC xTrue))]))
            val _ = defineX tab (xWhite,RHS_TEXT TXT_WHITE)
            val _ = defineX tab (xWhite,RHS_PI(TXT_UNDER,[(true,RE_REP(RE_BASIC xTrue))]))
            val _ = tab_ := tab
         in 
            (tab,xTrue,xWhite)
         end

      val initXTable = #1 o makeXTable
      val (_,xTrue,xWhite) = makeXTable()

      val XRE_UNDER = RE_REP(RE_BASIC xTrue)
      val XRE_WHITE = RE_REP(RE_BASIC xWhite)

      fun extractXTable tab = 
         let 
            val arr = extractDict tab
            val list = Array.foldri (fn (x,(_,(rs,_)),xrs) => (x,rs)::xrs) nil arr
         in 
            (Array.length arr,list)
         end

      fun X2xString tab x = Vector2String (Index2X tab x) 
         handle NoSuchIndex => "_"^Int.toString x
      fun X2String x = Vector2String (Index2X (!tab_) x)
   end
