step :: (Delta d, AAM aam) => d -> aam 
     -> StateSpace d aam -> StatSpace d aam
step d aam ss = eachInSet ss $ \ (c,e,s,t) -> 
  eachInSet (call d aam t c e s) $ \ (c',e',s') ->
    setSingleton (c',e',s',tick aam c' t)

