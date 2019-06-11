lambda :: Profunctor p => p a a -> (a -> b) -> p a b
lambda paa f = dimap id f paa

rho :: Profunctor p => p b b -> (a -> b) -> p a b
rho pbb f = dimap f id pbb