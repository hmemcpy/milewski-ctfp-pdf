factorizer : (a × b → c) → a → b → c
factorizer g = λ x → λ y → g (x , y)
