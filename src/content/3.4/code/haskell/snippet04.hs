class Monad m where 
    (>=>) :: (a -> m b) -> (b -> m c) -> (a -> m c)
    return :: a -> m a