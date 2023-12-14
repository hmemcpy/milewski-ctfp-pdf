length : List a → Const Int a
length [] = const 0ℤ
length (x ∷ xs) = const (1 + unConst (length xs))
