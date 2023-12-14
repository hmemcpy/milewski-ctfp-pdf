fmap f (safeHead (x ∷ xs)) = fmap f (Just x) = Just (f x)
