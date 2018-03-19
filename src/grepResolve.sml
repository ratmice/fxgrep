structure GrepCatParams =
   struct
      open CatError Errors GrepOptions UtilError 
	 
      fun catError(pos,err) = if !O_SILENT then () else TextIO.output
	 (!O_ERROR_DEVICE,formatMessage (4,!O_ERROR_LINEWIDTH) 
	  (Position2String pos^" Error in catalog:"::catMessage err))
   end

structure GrepResolve = ResolveCatalog (structure Params = GrepCatParams)
