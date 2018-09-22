runCont :: Cont r a -> (a -> r) -> r
runCont (Cont k) h = k h