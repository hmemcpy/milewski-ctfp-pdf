fmap f [] = []
fmap f (x:xs) = f x : fmap f xs