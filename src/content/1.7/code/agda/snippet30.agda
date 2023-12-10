square : Int → Int
square x = x * x

mis : Maybe (List Int)
mis = Just (+ 1 ∷ + 2 ∷ + 3 ∷ [])

mis2 : Maybe (List Int)
mis2 = fmap (fmap square) mis
