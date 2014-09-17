bindMany :: (AAM aam) => aam 
         -> Time aam -> [Name] -> [Atom] 
         -> Env aam -> Store d aam 
         -> Maybe (Env aam, Store d aam)
bindMany _   _ [] [] e s = Just (e, s)
bindMany aam t (x:xs) (xa:xas) e s = case bindMany aam t xs xas e s of
  Nothing -> Nothing
  Just (e', s') ->
    let l = alloc aam x t
    in Just (mapInsert x l e', mapInsertWith (\/) l xv s')
bindMany _ _ _ _ _ _ = Nothing
