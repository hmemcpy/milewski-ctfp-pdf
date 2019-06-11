safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:xs) = Just x