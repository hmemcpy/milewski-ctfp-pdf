module Section105 where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Int using (Int)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; id)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable
  ℓ ℓ' ℓ'' : Level
  a b c : Set
  f : a → b
  g : b → a

{- SECTION 5.1: INITIAL OBJECT ---------------------------------------------------}
{-                                                                   [snippet01] -}
absurd : ⊥ → a
absurd ()

{- SECTION 5.2: TERMINAL OBJECT --------------------------------------------------}
{-                                                                   [snippet02] -}
unit : a → ⊤
unit _ = tt

{-                                                                   [snippet03] -}
yes : a → Bool
yes _ = true

{-                                                                   [snippet04] -}
no : a → Bool
no _ = false

{- SECTION 5.4: ISOMORPHISMS -----------------------------------------------------}
{-                                                                   [snippet05] -}
_ : f ∘ g ≡ id
_ = {!!}   -- We leave an unfilled hole where a proof would normally go;
           -- here a proof is impossible since we don't know anything about f or g.
_ : g ∘ f ≡ id
_ = {!!}

{- SECTION 5.5: PRODUCTS ---------------------------------------------------------}

{- Syntax for Σ-types (see Data.Sum.Base of the Agda standard library)           -}
open import Agda.Builtin.Sigma hiding (module Σ)
  renaming (fst to proj₁; snd to proj₂)
module Σ = Agda.Builtin.Sigma.Σ
Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
infix 2 Σ-syntax

module snippet09 where
  p : c → a
  p = {!!}
  q : c → b
  q = {!!}

module snippet10 where
  p : Int → Int
  p x = x
  q : Int → Bool
  q _ = true

_×_ : ∀ (a : Set ℓ) (b : Set ℓ') → Set (ℓ ⊔ ℓ')
a × b = Σ[ x ∈ a ] b
infixr 2 _×_ _⋀_
_⋀_ = _×_
{-                                                                   [snippet06] -}
fst : a × b → a
fst (x , _) = x
{-                                                                   [snippet07] -}
snd : a × b → b
snd (_ , y) = y

module snippet11 where
  p : Int × Int × Bool → Int
  p (x , _ , _) = x           -- We're using pattern matching on triples here.
  q : Int × Int × Bool → Bool
  q (_ , _ , b) = b

module snippet13 where
  m : Int → Int × Bool
  m x = (x , true)
  -- Indeed, the two projections can be reconstructed as:
  p : Int → Int
  p x = fst (m x)
  q : Int → Bool
  q x = snd (m x)

module snippet14 where
  open snippet11
  m : Int × Int × Bool → Int × Bool
  m x = (p x , q x)
  -- Again, the two projections can be reconstructed as:
  p' : Int × Int × Bool → Int
  p' x = fst (m x)
  q' : Int × Int × Bool → Bool
  q' x = snd (m x)

module snippet20 where
  factorizer : (c → a) → (c → b) → c → a × b
  factorizer p q = λ x → (p x , q x)

{- The product a × b:

  a         b
  |\       /|
  |  p   q  |
  |   ↘ ↙   |
  p'   c    q'   (c = a × b = greatest lower bound of the set {a, b})
   \   |   /
    \  m  /
     ↘ ↓ ↙
       c'

The diagram illustrates the universal property that defines the product c. It is
the object that has projection maps p : c → a and q : c → b and is such that for
every other object c', with projection maps p' : c' → a, q' : c' → b there exists
a morphism m that factorizes p' and q' as follows: p' = p ∘ m and q' = q ∘ m.    -}

×-universal-property :  {c' : Set}(p' : c' → a)(q' : c' → b)
  →                     Σ[ m ∈ (c' → a × b) ]  p' ≡ fst ∘ m  ⋀  q' ≡ snd ∘ m

×-universal-property p' q' = (λ x → p' x , q' x) , refl , refl

{- 5.6 COPRODUCT -----------------------------------------------------------------}
{-                                                                   [snippet21]
i : a → c
j : b → c
                                                                     [snippet22]
i' = m ∘ i
j' = m ∘ j
                                                                     [snippet23] -}
data Contact : Set where
  PhoneNum : Nat → Contact
  EmailAddr : String → Contact
{-                                                                   [snippet24] -}
helpdesk : Contact
helpdesk = PhoneNum 2222222

{- The coproduct a + b -----------------------------------------------------------}
module coprod where
  data _+_ (a b : Set) : Set where
    i : a → a + b
    j : b → a + b
  factorizer : (a → c) → (b → c) → a + b → c
  factorizer i'  _   (i x) = i' x
  factorizer _   j'  (j y) = j' y
  {-
         c'
       ↗ ↑ ↖
      /  m  \
     /   |   \
    i'   c    j'   (c = a + b = least upper bound of the set {a, b})
    |   ↗ ↖   |
    |  i   j  |
    |/       \|
    a         b                                                                   -}

  +-universal-property :  {a b c' : Set} (i' : a → c')(j' : b → c')
    →                     Σ[ m ∈ (a + b → c') ]  i' ≡ m ∘ i  ⋀  j' ≡ m ∘ j

  +-universal-property i' j' = factorizer i' j' , refl , refl

{-                                                                   [snippet25] -}
data Either (a b : Set) : Set where
  Left : a → Either a b
  Right : b → Either a b
module snippet26 where
  factorizer : (a → c) → (b → c) → Either a b → c
  factorizer i j (Left x) = i x
  factorizer i j (Right y) = j y

