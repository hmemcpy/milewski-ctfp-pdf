ra >>= k = Reader (\e -> let a = runReader ra e
                             rb = k a
                         in runReader rb e)