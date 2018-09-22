runWriter :: Writer w a -> (a, w)
runWriter (Writer (a, w)) = (a, w)