toNat :: [()] -> Int
toNat = length

toLst :: Int -> [()]
toLst n = replicate n ()