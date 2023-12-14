\begin{code}
module Section-1-1 where

open import Data.Product using (_×_ ; _,_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable
  a b c d : Set

f : a → b
f = {!!}

g : b → c
g = {!!}

_ :  (f : a → b)
     (g : b → c)
     (h : c → d)
  →  (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

_ = λ f g h → refl

id : a → a
id x = x

_ : {f : a → b} → (f ∘ id ≡ f) × (id ∘ f ≡ f)
_ = refl , refl
\end{code}
