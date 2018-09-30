instance Monad [] where
    join = concat
    return x = [x]