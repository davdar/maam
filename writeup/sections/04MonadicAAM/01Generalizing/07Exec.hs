exec :: (Semantics d aam m) => d -> aam -> Call -> SS m Call
exec d aam c0 = iter (collect (step $ call d aam)) $ point c0
