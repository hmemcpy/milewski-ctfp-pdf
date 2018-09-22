(Writer (a, w)) >>= f = let Writer (b, w') = f a 
                        in Writer (b, w `mappend` w')