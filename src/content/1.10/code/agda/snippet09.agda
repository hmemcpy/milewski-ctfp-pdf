safeHead (fmap f (x ∷ xs)) = safeHead (f x ∷ fmap f xs) = just (f x)
