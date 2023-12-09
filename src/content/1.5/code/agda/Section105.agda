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
  a b : Level
  A B C : Set
  f : A → B
  g : B → A

{- SECTION 5.1: INITIAL OBJECT ---------------------------------------------------
The *initial object* is the object with exactly one morphism going from it to
any other object in the category. It is unique up to isomorphism (when it exists).
In the category of sets and functions, the initial object is the empty set.
In Agda, we represent the empty set by the empty type ⊥.             [snippet01] -}
absurd : ⊥ → A

{- `absurd` denotes a family of morphism from ⊥ to any object A in Set.
Agda already defines this family and denotes it by `⊥-elim`
(read "false elimination").                                                      -}
absurd ()

{- This is the familiar "ex falso quodlibet" principle: from a false premise
anything follows.                                                                -}

{- SECTION 5.2: TERMINAL OBJECT --------------------------------------------------}
{- The *terminal object* is the object with exactly one morphism coming to it from
any other object in the category. It is unique up to isomorphism (when it exists).
In the category of sets and functions, the terminal object is the singleton.
In Agda, we represent the singleton by the unit type ⊤.              [snippet02] -}
unit : A → ⊤
unit _ = tt

{- Here's another morphism (in Set) from any object to the two element set Bool:
                                                                     [snippet03] -}
yes : A → Bool
yes _ = true

{- but Bool does not meet the uniqueness criterion of terminal object, as there
are other morphisms from every set to Bool; e.g.,                    [snippet04] -}
no : A → Bool
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
{- The *product* of two objects `A` and `B` is an object `A × B` together with two
morphisms `π₁ : A × B → A` and `π₂ : A × B → B` such that for any object `C`
and morphisms `f : C → A`, `g : C → B` there is a unique morphism `h : C → A × B`
such that `f ≡ π₁ ∘ h` and `g ≡ π₂ ∘ h`.                                         -}

------------------------------------------------------------------------
-- Syntax for Σ-types (see Data.Sum.Base of the Agda standard library)
open import Agda.Builtin.Sigma hiding (module Σ) renaming (fst to proj₁; snd to proj₂)
module Σ = Agda.Builtin.Sigma.Σ
Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
infix 2 Σ-syntax

{- Let's try to define a pattern of objects and morphisms in the category of sets
that will lead us to the construction of a product of two sets, `A` and `B`. This
pattern consists of an object `C` and two morphisms `p` and `q` connecting it to
`A` and `B`, respectively:                                           [snippet09] -}
module snippet09 where
  p : C → A
  p = {!!}
  q : C → B
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
triple.

Actually, this is an unfortunate example since it requires that we already know
how to construct products. Let's pretend we don't and just take the following
definition for granted for now.                                                  -}
_×_ : ∀ (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B
infixr 2 _×_ _⋀_
_⋀_ = _×_

{-                                                                   [snippet06] -}
fst : A × B → A
fst (x , _) = x
{-                                                                   [snippet07] -}
snd : A × B → B
snd (_ , y) = y

{- Here are two morphisms that make this example a legitimate
candidate for the product `Int × Bool`:                              [snippet11] -}
module snippet11 where
  p : Int × Int × Bool → Int
  p (x , _ , _) = x           -- We're using pattern matching on triples here.
  q : Int × Int × Bool → Bool
  q (_ , _ , b) = b

{- But we want the "best" candidate `C`---i.e., the `C` such that for all other
such candidates, say, `C'`, there is a morphism `m : C' → C` such that p' = p ∘ m
and q' = q ∘ m. See the figure below.

Another way of looking at these equations is that m factorizes p' and q'. To build
some intuition, let's see that the pair `Int × Bool` with the two canonical
projections, `fst` and `snd` is indeed better than the two candidates presented
before. The mapping `m` for the first candidate is:                 [snippet13]  -}
module snippet13 where
  m : Int → Int × Bool
  m x = (x , true)

  -- Indeed, the two projections can be reconstructed as:
  p : Int → Int
  p x = fst (m x)
  q : Int → Bool
  q x = snd (m x)

{- The m for the second example, `C' = Int × Int × Bool` is similarly uniquely
determined:                                                         [snippet14]  -}
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
  factorizer : (C → A) → (C → B) → C → A × B
  factorizer p q = λ x → (p x , q x)

{- The product A × B:

  A         B
  |\       /|
  |  p   q  |
  |   ↘ ↙   |
  p'   C    q'   (C = A × B = greatest lower bound of {A, B})
   \   |   /
    \  m  /
     ↘ ↓ ↙
       C'

The diagram illustrates the universal property that defines the product C. It is
the object that has projection maps p : C → A and q : C → B and is such that for
every other object C', with projection maps p' : C' → A, q' : C' → B there exists
a morphism m that factorizes p' and q' as follows: p' = p ∘ m and q' = q ∘ m.    -}

×-universal-property :  {C' : Set}(p' : C' → A)(q' : C' → B)
  →                     Σ[ m ∈ (C' → A × B) ]  p' ≡ fst ∘ m  ⋀  q' ≡ snd ∘ m

×-universal-property p' q' = (λ x → p' x , q' x) , refl , refl

{- 5.6 COPRODUCT -}
{- Like every construction in category theory, the product has a dual, which is
called the coproduct. When we reverse the arrows in the product pattern, we end up
with an object C equipped with two injections, inl and inr: morphisms from A to C
and from B to C. In Agda, these are often denoted by inj₁ and inj₂, but we'll
denote them by i and j as in the text.

Again, we want the "best" candidate C, but the ranking is inverted: object C is
"better" than object C' equipped with the injections i' and j' if there is a
morphism m from C to C' that factorizes the injections:
-}
data _+_ (A B : Set) : Set where
  i : A → A + B
  j : B → A + B

factorizer : (A → C) → (B → C) → A + B → C
factorizer i'  _   (i a) = i' a
factorizer _   j'  (j b) = j' b

{-                                                                   [snippet23] -}
data Contact : Set where
  PhoneNum : Nat → Contact
  EmailAddr : String → Contact

helpdesk : Contact
helpdesk = PhoneNum 2222222



{- The coproduct A + B.

         C'
       ↗ ↑ ↖
      /  m  \
     /   |   \
    i'   C    j'   (C = A + B = least upper bound of {A, B})
    |   ↗ ↖   |
    |  i   j  |
    |/       \|
    A         B

-}

+-universal-property :  {A B C' : Set} (i' : A → C')(j' : B → C')
  →                     Σ[ m ∈ (A + B → C') ]  i' ≡ m ∘ i  ⋀  j' ≡ m ∘ j

+-universal-property {A}{B}{C'} i' j' = m , refl , refl
  where
  m : A + B → C'
  m (i a) = i' a
  m (j b) = j' b
