fmap-id : (x : Maybe A) → fmap id x ≡ id x
fmap-id Nothing = refl
fmap-id (Just x) = refl
