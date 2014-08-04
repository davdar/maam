step :: StateSpace -> StateSpace
step Nothing = Nothing
step (Just (c, e)) = call e c

exec :: Call -> StateSpace
exec c0 = iter step $ Just (c0, mapEmpty)
