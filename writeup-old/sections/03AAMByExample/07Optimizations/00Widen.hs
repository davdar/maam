widen :: StateSpace d aam -> StateSpace d aam
widen ss =
  let wideStore = setJoins $ setMap (\ (_,_,s,_) -> s) ss
  in setMap (\ (c,e,_,t) -> (c,e,wideStore,t))

wideStep :: (Delta d, AAM aam) => d -> aam 
         -> StateSpace d aam -> StateSpace d aam
wideStep d aam = widen . step d aam

widenExec :: (Delta d, AAM aam) => d -> aam 
          -> Call -> StateSpace d aam
widenExec d aam c0 = iter (collect (wideStep d aam)) $ 
  setSingleton (c0, mapEmpty, mapEmpty, tzero aam)
