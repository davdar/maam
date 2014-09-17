data C_Delta = C_Delta
data ConcreteVal aam = LitV Lit | Clo [Name] Call (Env aam)
instance Delta C_Delta where
  type Val C_Delta = ConcreteVal
  lit C_Delta l = Lit l
  clo C_Delta xs c e = Clo xs c e
  op C_Delta Add1 (LitV (I i)) = Just $ LitV $ I $ i+1
  op C_Delta Sub1 (LitV (I i)) = Just $ LitV $ I $ i-1
  op C_Delta IsNonNeg (LitV (I i)) 
    | i >= 0 = Just $ LitV $ B $ True
    | otherwise = Just $ LitV $ B $ False
  op C_Delta _ _ = Nothing
  elimBool C_Delta (LitV (B b)) = setSingleton b
  elimBool C_Delta _ = setEmpty
  elimClo C_Delta (Clo xs c e) = setSingleton (xs, c, e)
  elimClo C_Delta _ = setEmpty
