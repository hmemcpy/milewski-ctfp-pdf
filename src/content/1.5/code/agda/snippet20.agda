factorizer : (c → a) → (c → b) → c → a × b
factorizer p q = λ x → (p x , q x)
