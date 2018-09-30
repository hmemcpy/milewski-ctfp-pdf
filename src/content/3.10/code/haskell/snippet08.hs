pi :: Profunctor p => forall c. (forall a. p a a) -> p c c
pi e = e