module Section211 where

private variable
  a b c : Set

-- non-dependent version
_∘_ : (b → c) → (a → b) → a → c
f ∘ g = λ x → f (g x)

module snippet01 {g : a → b}{f : b → c} where
  h : a → c
  h = f ∘ g

module snippet02 {f : a → b}{g : b → c} where
  h : a → c
  h x = let y = f x
        in g y

-- dependent version
_∘ᵈ_ :  ∀{ℓ₁ ℓ₂ ℓ₃}{a : Set ℓ₁}{b : a → Set ℓ₂}{c : {x : a} → b x → Set ℓ₃}
  →     (∀{x}(y : b x) → c y) → (g : (x : a) → b x)
  →     ((x : a) → c (g x))
f ∘ᵈ g = λ x → f (g x)
