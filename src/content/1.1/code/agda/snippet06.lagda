\begin{code}[hide]
open import Relation.Binary.PropositionalEquality  using (_≡_ ; module ≡-Reasoning)
open import Data.Product using (_×_ ; _,_)
id : ∀{A : Set} → A → A
id a = a
_∘_ : {A B C : Set}(g : B → C)(f : A → B) → A → C
g ∘ f = λ a → g (f a)
open ≡-Reasoning
\end{code}
\begin{code}
_ : ∀{A B : Set}{f : A → B} → (f ∘ id ≡ f) × (id ∘ f ≡ f)
_ = _≡_.refl , _≡_.refl
\end{code}
