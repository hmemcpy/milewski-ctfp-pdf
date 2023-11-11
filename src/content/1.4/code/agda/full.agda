open import Data.String
open import Data.Product

variable a b : Set

Writer : Set → Set
Writer a = ( a × String )

morphism : ∀ (a b : Set) → a → Writer b
morphism = {!   !}

_>=>_ : ∀ {a b c : Set} → (a → Writer b) → (b → Writer c) → (a → Writer c)
m1 >=> m2 = λ x ->
  let (y , s1) = m1 x
      (z , s2) = m2 y
  in (z , s1 ++ s2)

return : ∀ {a : Set} → a → Writer a
return x = (x , "")
