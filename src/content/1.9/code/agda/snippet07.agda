curry : (a × b → c) → a → b → c
curry f x y = f (x , y)
-- (refusing to use "a" and "b" to name inhabitants of types a and b!)
