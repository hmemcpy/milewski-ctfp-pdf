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
{- The *initial object* is the object with exactly one morphism going from it to
any other object in the category. It is unique up to isomorphism (when it exists).
In the category of sets and functions, the initial object is the empty set.
In Agda, we represent the empty set by the empty type ⊥.             [snippet01] -}
absurd : ⊥ → a
{- absurd denotes a family of morphism from ⊥ to any object a in Set.  Agda
already defines this family and denotes it by ⊥-elim (read "false elimination").                                                      -}
absurd ()
{- This is the familiar "ex falso quodlibet" principle: from a false premise
anything follows.                                                                -}

{- SECTION 5.2: TERMINAL OBJECT --------------------------------------------------}
{- The *terminal object* is the object with exactly one morphism coming to it from
any other object in the category. It is unique up to isomorphism (when it exists).
In the category of sets and functions, the terminal object is the singleton.
In Agda, we represent the singleton by the unit type ⊤.              [snippet02] -}
unit : a → ⊤
unit _ = tt

{- Here's another morphism (in Set) from any object to the two element set Bool:
                                                                     [snippet03] -}
yes : a → Bool
yes _ = true

{- but Bool does not meet the uniqueness criterion of terminal object, as there
are other morphisms from every set to Bool; e.g.,                    [snippet04] -}
no : a → Bool
no _ = false

{- SECTION 5.4: ISOMORPHISMS -----------------------------------------------------}
{- Morphism 𝑔 is the inverse of morphism 𝑓 if their composition is the identity
morphism. These are actually two equations because there are two ways of composing
two morphisms:                                                       [snippet05] -}
_ : f ∘ g ≡ id
_ = {!!}   -- We leave an unfilled hole where a proof would normally go;
           -- here a proof is impossible since we don't know anything about f or g.
_ : g ∘ f ≡ id
_ = {!!}

{- SECTION 5.5: PRODUCTS ---------------------------------------------------------}
{- The *product* of two objects a and b is an object a × b together with two
morphisms π₁ : a × b → a and π₂ : a × b → b such that for any object c and
morphisms f : c → a, g : c → b there is a unique morphism h : c → a × b such that
f ≡ π₁ ∘ h and g ≡ π₂ ∘ h.                                                       -}

{- Syntax for Σ-types (see Data.Sum.Base of the Agda standard library)           -}
open import Agda.Builtin.Sigma hiding (module Σ)
  renaming (fst to proj₁; snd to proj₂)
module Σ = Agda.Builtin.Sigma.Σ
Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
infix 2 Σ-syntax

{- Let's try to define a pattern of objects and morphisms in the category of sets
that will lead us to the construction of a product of two sets, a and b. This
pattern consists of an object c and two morphisms p and q connecting it to
a and b, respectively:                                               [snippet09] -}
module snippet09 where
  p : c → a
  p = {!!}
  q : c → b
  q = {!!}

{- All Cs that fit this pattern will be considered candidates for the product.
There may be lots of them. For instance, let's pick, as our constituents, two
Haskell types, Int and Bool, and get a sampling of candidates for their product.
Here's one: Int. Can Int be considered a candidate for the product of Int and
Bool? Yes, it can, and here are its projections:                     [snippet10] -}
module snippet10 where
  p : Int → Int
  p x = x
  q : Int → Bool
  q _ = true

{- Here's another one: Int × Int × Bool. It's a tuple of three ele ments, or a
triple. Actually, this is an unfortunate example since it requires that we already
know how to construct products. Let's pretend we don't and just take the following
definition for granted for now.                                                  -}
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
{- Here are two morphisms that make this example a legitimate
candidate for the product Int × Bool:                                [snippet11] -}
module snippet11 where
  p : Int × Int × Bool → Int
  p (x , _ , _) = x           -- We're using pattern matching on triples here.
  q : Int × Int × Bool → Bool
  q (_ , _ , b) = b
{- But we want the "best" candidate c---i.e., the c such that for all other
such candidates, say, c', there is a morphism m : c' → c such that p' = p ∘ m
and q' = q ∘ m. See the figure below.

Another way of looking at these equations is that m factorizes p' and q'. To build
some intuition, let's see that the pair Int × Bool with the two canonical
projections, fst and snd is indeed better than the two candidates presented
before. The mapping m for the first candidate is:                    [snippet13] -}
module snippet13 where
  m : Int → Int × Bool
  m x = (x , true)
  -- Indeed, the two projections can be reconstructed as:
  p : Int → Int
  p x = fst (m x)
  q : Int → Bool
  q x = snd (m x)
{- The m for the second example, c' = Int × Int × Bool is similarly uniquely
determined:                                                          [snippet14] -}
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
{- Like every construction in category theory, the product has a dual, which is
called the coproduct. When we reverse the arrows in the product pattern, we end up
with an object c equipped with two injections, inl and inr: morphisms from a to c
and from b to c. In Agda, these are often denoted by inj₁ and inj₂, but we'll
denote them by i and j as in the text.

Again, we want the "best" candidate c, but the ranking is inverted: object c is
"better" than object c' equipped with the injections i' and j' if there is a
morphism m from c to c' that factorizes the injections:
                                                                     [snippet21]
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
