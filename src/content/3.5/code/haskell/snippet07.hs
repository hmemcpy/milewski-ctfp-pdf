runReader :: Reader e a -> e -> a
runReader (Reader f) e = f e