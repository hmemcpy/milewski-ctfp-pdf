factorizer : (C → A) → (C → B) → C → A × B
factorizer p q = λ x → (p x , q x)
