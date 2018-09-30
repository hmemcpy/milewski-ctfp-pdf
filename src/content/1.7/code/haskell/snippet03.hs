f' :: Maybe a -> Maybe b
f' Nothing = Nothing
f' (Just x) = Just (f x)