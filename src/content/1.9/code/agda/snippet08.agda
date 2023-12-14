uncurry : (a → b → c) → a × b → c
uncurry f (x , y) = f x y
