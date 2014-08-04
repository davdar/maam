atom :: (Delta d) => d 
     -> Env aam -> Store d aam -> Atom -> Set (Val d aam)
atom d _ _ (LitA l) = setSingleton $ lit d l
atom _ e s (Var x) = case mapLookup x e of
  Nothing -> setEmpty
  Just l -> mapLookup l s
atom d e s (Prim o a) = eachInSet (atom d e s a) $ \ v ->
  case op d o v of
    Nothing -> setEmpty
    Just v' -> setSingleton v'
atom d e _ (Lam xs c) = setSingleton $ clo d xs c e
