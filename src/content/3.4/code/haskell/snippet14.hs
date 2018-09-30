class Functor m => Monad m where
    join :: m (m a) -> m a
    return :: a -> m a