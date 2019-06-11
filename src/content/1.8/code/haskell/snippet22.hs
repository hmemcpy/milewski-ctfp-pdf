instance Functor (Reader r) where
    fmap f g = f . g