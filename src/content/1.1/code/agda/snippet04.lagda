\begin{code}[hide]
open import Relation.Binary.PropositionalEquality  using (_≡_ ; module ≡-Reasoning)
_∘_ : ∀{A B C : Set}(g : B → C)(f : A → B) → A → C
g ∘ f = λ a → g (f a)
open ≡-Reasoning
\end{code}
\begin{code}
_ :  ∀{A B C D : Set}
     (f : A → B)
     (g : B → C)
     (h : C → D)
  →  (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

_ = λ f g h → _≡_.refl
\end{code}
