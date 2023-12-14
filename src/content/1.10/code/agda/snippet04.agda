safeHead : List a → Maybe a
safeHead [] = nothing
safeHead (x ∷ xs) = just x
