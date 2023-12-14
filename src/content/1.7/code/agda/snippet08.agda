fmap-id : (x : Maybe a) → fmap id x ≡ id x
fmap-id Nothing = refl
fmap-id (Just x) = refl
