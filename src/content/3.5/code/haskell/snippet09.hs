ra >>= k = Reader (\e -> let a = runReader ra e
                         in ...)