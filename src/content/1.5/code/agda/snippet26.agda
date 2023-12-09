factorizer' : (A → C) → (B → C) → Either A B → C
factorizer' i j (Left a) = i a
factorizer' i j (Right b) = j b
