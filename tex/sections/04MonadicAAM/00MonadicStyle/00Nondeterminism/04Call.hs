call :: (Delta d, AAM aam) => d -> aam 
     -> Time aam -> Env aam -> Store d aam -> Call 
     -> Nondet (Call, Env aam, Store d aam)
call d aam t e s (If a tc fc) = do
  v <- atom d e s a
  b <- setMSum (elimBool d v)
  return (if b then tc else fc, e, s)
call d aam t e s (App fa xas) =
  v <- atom d e s fa
  (xs,c,e') <- setMSum $ elimClo d v
  mFromMaybe $ bindMany aam t xs xas e' s
call _ _ _ e s (Halt a) = return (Halt a, e, s)
