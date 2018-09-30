instance Functor (Reader e) where
    fmap f (Reader g) = Reader (\x -> f (g x))