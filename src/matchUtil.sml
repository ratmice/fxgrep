signature MatchUtil =
   sig
      val sortInt       : int list -> int list
      val selectIntList : int list * (int * 'a) list -> 'a list
   end

structure MatchUtil : MatchUtil =
   struct
      val sortInt = GramUtil.sortInt

      fun selectIntList (nil,_) = nil
        | selectIntList (_,nil) = nil
        | selectIntList (is as i::is1,jas as (j,a)::jas1) =
         case Int.compare (i,j) 
           of LESS => selectIntList (is1,jas)
                  | EQUAL => a::selectIntList (is1,jas1)
                  | GREATER => selectIntList(is,jas1)

   end
