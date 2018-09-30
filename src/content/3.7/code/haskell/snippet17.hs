instance Functor Stream where
    fmap f (Cons a as) = Cons (f a) (fmap f as)