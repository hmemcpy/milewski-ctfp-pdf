(=>=) :: (Product e a -> b) -> (Product e b -> c) -> (Product e a -> c)
f =>= g = \(P e a) -> let b = f (P e a)
                          c = g (P e b) 
                      in c