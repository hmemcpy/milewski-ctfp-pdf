fmap f (safeHead (x ∷ xs)) = fmap f (just x) = just (f x)
