call :: (Delta d, AAM aam) => d -> aam 
     -> Time aam -> Env aam -> Store d aam -> Call 
     -> Set (Call, Env aam, Store d aam)
call d aam t e s (If a tc fc) =
  eachInSet (atom d e s a) $ \ v -> 
    eachInSet (elimBool d v) $ \ b -> 
      setSingleton (if b then tc else fc, e, s)
call d aam t e s (App fa xas) =
  eachInSet (atom d e s fa) $ \ v ->
    eachInSet (elimClo d v) $ \ (xs,c,e') ->
      setFromMaybe $ bindMany aam t xs xas e' s
call _ _ _ e s (Halt a) = setSingleton (Halt a, e, s)
