f' : Maybe A → Maybe B
f' Nothing = Nothing
f' (Just x) = Just (f x)
