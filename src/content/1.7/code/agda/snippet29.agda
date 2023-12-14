maybeTail : List a → Maybe (List a)
maybeTail [] = Nothing
maybeTail (x ∷ xs) = Just xs
