fromY :: (a -> x) -> b -> x
fromY f b = f (btoa b)