\begin{code}
module Section-1-1 where

open import Data.Product using (_×_ ; _,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

private variable
  A B C D : Set

f : A → B
f = {!!}

g : B → C
g = {!!}

_ :  (f : A → B)
     (g : B → C)
     (h : C → D)
  →  (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

_ = λ f g h → _≡_.refl

id : A → A
id a = a

_ : {f : A → B} → (f ∘ id ≡ f) × (id ∘ f ≡ f)
_ = _≡_.refl , _≡_.refl
\end{code}
