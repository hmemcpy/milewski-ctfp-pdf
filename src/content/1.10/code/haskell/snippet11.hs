fmap f Nothing = Nothing
fmap f (Just x) = Just (f x)