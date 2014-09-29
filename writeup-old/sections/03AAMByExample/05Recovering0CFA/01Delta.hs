data Sym_Delta = Sym_Delta
data SymVal aam = IntV | BoolV | Clo [Name] Call (Env aam)
instance Delta Sym_Delta where
  type Val Sym_Delta = SymVal
  lit Sym_Delta (I _) = IntV
  lit Sym_Delta (B _) = BoolV
  clo Sym_Delta xs c e = Clo xs c e
  op Sym_Delta Add1 IntV = Just IntV
  op Sym_Delta Sub1 IntV = Just IntV
  op Sym_Delta IsNonNeg IntV = Just BoolV 
  op Sym_Delta _ _ = Nothing
  elimBool Sym_Delta BoolV = setSingleton True \/ setSingleton False
  elimBool Sym_Delta _ = setEmpty
  elimClo Sym_Delta (Clo xs c e) = setSingleton (xs, c, e)
  elimClo Sym_Delta _ = setEmpty
