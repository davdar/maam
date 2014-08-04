step :: (Delta d, AAM aam) => d -> aam 
     -> StateSpace d aam -> StatSpace d aam
step d aam ss = eachInSet ss $ \ (c,e,s,t) -> 
  eachInSet (call d aam t c e s) $ \ (c',e',s') ->
    setSingleton (c',e',s',tick aam c' t)

exec :: (Delta d, AAM aam) => d -> aam 
     -> Call -> StateSpace d aam
exec d aam c0 = iter (collect (step d aam)) $ 
  setSingleton (c0, mapEmpty, mapEmpty, tzero aam)
