atom :: Env -> Atom -> Maybe Val
atom _ (LitA l) = Just $ LitV l
atom e (Var x) = mapLookup x e
atom e (Prim o a) = case atom e a of
  Nothing -> Nothing
  Just v -> op o v
atom e (Lam xs c) = Just $ Clo xs c e
