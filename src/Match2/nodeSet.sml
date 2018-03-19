structure Node = 
  struct
    type Node = ErrorData.Position * MatchData.Tree

    fun compare 
      (((_,line1,col1),_),((_,line2,col2),_)) =
      if line1=line2 then Int.compare (col1,col2)
      else Int.compare (line1,line2)
  end

structure NodeSet = ListSetFn (type ord_key=Node.Node
			       val compare=Node.compare)