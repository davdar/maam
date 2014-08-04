call :: (Delta d, AAM aam) => d -> aam -> Call -> M d aam Call
call d aam (If a tc fc) = do
  v <- atom a
  b <- setMSum (elimBool d v)
  return $ if b then tc else fc
call d aam (App fa xas) =
  v <- atom d aam fa
  (xs,c,e') <- setMSum $ elimClo d v
  mFromMaybe $ bindMany aam xs xas e'
call _ _ (Halt a) = return $ Halt a
