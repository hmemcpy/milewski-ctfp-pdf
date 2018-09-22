flip :: (a -> b -> c) -> (b -> a -> c)
flip f y x = f x y