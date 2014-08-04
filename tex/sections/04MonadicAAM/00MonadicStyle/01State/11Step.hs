step :: (Delta d, AAM aam) => d -> aam 
     -> StateSpace d aam -> StatSpace d aam
step d aam ss = eachInSet ss $ \ (c,e,s,t) -> setFromList $ do
  (((c',e'),s'),t') <-
    flip runStateT e $
    flip runStateT s $
    flip runStateT t $
    call d aam c
  return (c',e',s',tick aam c' t)
