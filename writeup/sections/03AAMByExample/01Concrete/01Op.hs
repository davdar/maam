op :: Op -> Val -> Maybe Val
op Add1 (LitV (I n)) = Just $ LitV $ I $ n+1
op Sub1 (LitV (I n)) = Just $ LitV $ I $ n-1
op IsNonNeg (LitV (I n)) | n >= 0 = Just $ LitV $ B True
                         | otherwise = Just $ LitV $ B False
op _ _ = Nothing
