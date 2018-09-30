return :: a -> Writer a
return x = (x, "")