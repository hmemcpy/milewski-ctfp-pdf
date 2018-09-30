class Monad m where
    (>>=) :: m a -> (a -> m b) -> m b
    return :: a -> m a