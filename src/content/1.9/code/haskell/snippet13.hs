eval :: ((a -> b), a) -> b
eval (f, x) = f x