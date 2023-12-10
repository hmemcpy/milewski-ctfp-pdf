maybeTail : List A → Maybe (List A)
maybeTail [] = Nothing
maybeTail (x ∷ xs) = Just xs
