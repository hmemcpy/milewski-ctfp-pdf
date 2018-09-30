instance Bifunctor (,) where 
    bimap f g (x, y) = (f x, g y)