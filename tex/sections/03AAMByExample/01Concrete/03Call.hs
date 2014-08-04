call :: Env -> Call -> Maybe (Call, Env)
call e (If a tc fc) = case atom e a of
  Just (LitV (B True)) -> Just (tc, e)
  Just (LitV (B False)) -> Just (fc, e)
  _ -> Nothing
call e (App fa xas) =
  case atom e fa of
    Just (Clo xs c e') ->
      case bindMany xs xas e' of
        Nothing -> Nothing
        Just e'' -> Just (c, e'')
    _ -> Nothing
call e (Halt a) = Just (Halt a, e)
