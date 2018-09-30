(>>) :: m a -> m b -> m b
m >> k = m >>= (\_ -> k)