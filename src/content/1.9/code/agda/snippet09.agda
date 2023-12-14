factorizer : (a × b → c) → a → b → c
factorizer g = λ x → (λ y → g (x , y))
-- (Again, we won't use "a" and "b" to label inhabitants of a and b!)
