instance Monad Maybe where
    Nothing >>= k = Nothing
    Just a  >>= k = k a
    return a = Just a