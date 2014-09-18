atom :: (Delta d) => d 
     -> Env aam -> Store d aam -> Atom -> Nondet (Val d aam)
atom d _ _ (LitA l) = return $ lit d l
atom _ e s (Var x) = case mapLookup x e of
  Nothing -> mzero
  Just l -> setMSum $ mapLookup l s
atom d e s (Prim o a) = do
  v <- atom d e s a
  mFromMaybe $ op d o v
atom d e _ (Lam xs c) = return $ clo d xs c e

