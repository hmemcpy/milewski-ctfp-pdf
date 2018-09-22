instance Functor ((->) r) where
    fmap f g = f . g