return : ∀ {a : Set} → a → Writer a
return x = (x , "")
