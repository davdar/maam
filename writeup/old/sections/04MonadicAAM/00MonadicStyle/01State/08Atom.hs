atom :: (Delta d) => d -> aam -> Atom -> M d aam (Val d aam)
atom d aam (LitA l) = return $ lit d l
atom d aam (Var x) = do
  e <- get $ E aam
  s <- get $ S d aam
  case mapLookup x e of
    Nothing -> mzero
    Just l -> setMSum $ mapLookup l s
atom d aam (Prim o a) = do
  v <- atom d aam a
  mFromMaybe $ op d o v
atom d aam (Lam xs c) = do
  e <- get $ E aam
  return $ clo d xs c e
