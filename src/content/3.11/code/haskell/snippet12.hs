instance Functor (FreeF f) where
    fmap g (FreeF r) = FreeF (\bi -> r (bi . g))