-- dependent version
_∘_ :  ∀{a b c}{A : Set a}{B : Set b}{C : Set c}
  →    (f : B → C) → (g : A → B)
  →    A → C
f ∘ g = λ x → f (g x)

-- dependent version
_∘ᵈ_ :  ∀{a b c}{A : Set a}{B : A → Set b}{C : {x : A} → B x → Set c}
  →     (∀{x}(y : B x) → C y) → (g : (x : A) → B x)
  →     ((x : A) → C (g x))
f ∘ᵈ g = λ x → f (g x)
