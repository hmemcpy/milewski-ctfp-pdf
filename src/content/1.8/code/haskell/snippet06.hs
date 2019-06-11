instance Functor Identity where
    fmap f (Identity x) = Identity (f x)