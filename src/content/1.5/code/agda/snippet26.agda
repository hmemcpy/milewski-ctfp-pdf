factorizer : (a → c) → (b → c) → Either a b → c
factorizer i j (Left x) = i x
factorizer i j (Right y) = j y
