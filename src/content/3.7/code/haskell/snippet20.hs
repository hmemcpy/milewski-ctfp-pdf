instance Comonad Stream where
    extract (Cons a _) = a 
    duplicate (Cons a as) = Cons (Cons a as) (duplicate as)