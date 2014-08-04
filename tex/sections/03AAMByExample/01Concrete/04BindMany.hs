bindMany :: [Name] -> [Atom] -> Env -> Maybe Env
bindMany [] [] e = Just e
bindMany (x:xs) (xa:xas) e = 
  case (atom xa e, bindMany xs xas e) of
    (Just xv, Just e') -> Just (mapInsert x xv e')
    _ -> Nothing
bindMany _ _ _ = Nothing
