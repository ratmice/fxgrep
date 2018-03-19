signature DocDtd = 
  sig
    include Dtd
    
    val piGi           : UniChar.Data
    val attrsGi        : UniChar.Data
    val contentGi      : UniChar.Data
    val targetAtt      : UniChar.Data
    val piIdx          : int
    val attrsIdx       : int
    val contentIdx     : int
    val targetIdxA     : int
    val targetIdxE     : int

    val initDocDtd     : unit -> Dtd 

    val Element2Doc    : Dtd -> UniChar.Data -> int
    val Doc2Element    : Dtd -> int -> UniChar.Data

    val DocAtt2Elem    : Dtd -> int -> int
    val DocElem2Att    : Dtd -> int -> int

    val DocElem2xString : Dtd -> int -> string
    val DocElem2String  : int -> string
  end

structure DocDtd0 =
  struct

    open Dtd
    open UniChar GrepOptions

    val piGi      = String2Data "#pi"
    val attrsGi   = String2Data "#attrs"
    val contentGi = String2Data "#content"
    val targetAtt = String2Data "#target"


    val dtd_ = ref (Dtd.initDtdTables())

    fun initDtdTables() = 
      let 
	val dtd = Dtd.initDtdTables()
	val _ = Element2Index dtd piGi
	val _ = Element2Index dtd attrsGi
	val _ = Element2Index dtd contentGi
	val _ = Element2Index dtd targetAtt
	val _ = AttNot2Index dtd targetAtt
	val _ = dtd_ := dtd 
      in 
	dtd
      end

    val initDocDtd = initDtdTables

    local
      val dtd = initDtdTables()
    in 
      val piIdx      = Element2Index dtd piGi
      val attrsIdx   = Element2Index dtd attrsGi
      val contentIdx = Element2Index dtd contentGi
      val targetIdxE = Element2Index dtd targetAtt
      val targetIdxA = AttNot2Index dtd targetAtt
    end

    val Attribute2Doc = AttNot2Index
    val Element2Doc   = Element2Index
    val Doc2Element   = Index2Element

    fun DocAtt2Elem dtd i = Element2Index dtd (Index2AttNot dtd i)
    fun DocElem2Att dtd i = AttNot2Index dtd (Index2Element dtd i)

    fun DocAtt2xString dtd i  = Data2String (Index2AttNot dtd i) 
    fun DocElem2xString dtd i = Data2String (Index2Element dtd i)

    fun DocAtt2String a = DocAtt2xString (!dtd_) a
    fun DocElem2String e = DocElem2xString (!dtd_) e
  end

structure DocDtd = DocDtd0 : DocDtd