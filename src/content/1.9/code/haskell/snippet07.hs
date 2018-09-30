curry :: ((a, b) -> c) -> (a -> b -> c)
curry f a b = f (a, b)