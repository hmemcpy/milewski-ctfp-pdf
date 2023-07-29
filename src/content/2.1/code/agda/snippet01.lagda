\begin{code}
-- non-dependent version
_∘_  : {A : Set}{B : Set}{C : Set}
     → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

-- dependent version
_∘ᵈ_  : {A : Set}{B : A → Set}{f : {x : A} → B x → Set}
      → (∀{x}(y : B x) → f y) → (g : (x : A) → B x)
      → ((x : A) → f (g x))
f ∘ᵈ g = λ x → f (g x)
\end{code}
