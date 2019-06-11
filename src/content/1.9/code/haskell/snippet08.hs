uncurry :: (a -> b -> c) -> ((a, b) -> c)
uncurry f (a, b) = f a b