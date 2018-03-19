structure MatchData =
   struct
      type AttSpc = int * UniChar.Vector
      datatype Tree =
	 T_ELEM of int * AttSpc vector * Content
       | T_TEXT of UniChar.Vector
       | T_PI of UniChar.Vector * Content
      withtype Content = (Errors.Position * Tree) vector

      datatype MatchTree = MTREE of (int list * MatchForest)
      withtype MatchForest = MatchTree array
      val emptyMatchForest:MatchForest = Array.fromList nil

      val emptyContent = Vector.fromList nil : Content
      datatype MatchSelect = 
         ALL
       | INNER 
       | OUTER 

      type Match = Errors.Position * Tree
      datatype Matches = 
         ONE of Match 
       | MORE of Match option * Matches list

      type 'a Collector = (Match * 'a -> 'a)

      datatype Label = LABEL of int * int * int * int * int * Labeling 
      withtype Labeling = Label vector
      val emptyLabeling = Vector.fromList nil : Labeling

      datatype Passes =
	SINGLE of PreAlg.PreAlg 
      | DOUBLE of PreArgBlg.PreArgBlg

   end
