instance Functor (Reader a) where
    fmap f h = f . h