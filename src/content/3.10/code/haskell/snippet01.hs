class Profunctor p where
    dimap :: (c -> a) -> (b -> d) -> p a b -> p c d