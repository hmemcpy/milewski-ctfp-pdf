instance Functor (FreeF f) where
    fmap g (FMap h fi) = FMap (g . h) fi