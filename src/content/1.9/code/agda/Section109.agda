module Section109 where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Float using (Float) renaming (_<ᵇ_ to _<ᶠᵇ_)
open import Data.Integer using (ℤ; 0ℤ)
open import Data.Nat.Base as ℕ using ()
open import Data.Product using (_×_; _,_; Σ-syntax) renaming (dmap′ to _⟨∘⟩_)
open import Data.String using (String; _++_)
open import Function using (_∘_; _∘₂_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


private variable a b c d e : Set

{- 9 Function Types  -------------------------------------------------------------}

{- 9.1 Universal Construction ----------------------------------------------------}
{- Paraphrasing the text:

   We will need a pattern that involves three objects: the function type that we
   are constructing, the domain type, and the codomain type.  The obvious pattern
   that connects these three types is called *function application* or
   *evaluation*. Given a candidate for a function type, let's call it z (an
   object) and the domain type a (an object), the application maps this pair (z,
   a) to the codomain type object b.  Thus, we have three objects, z, a, and b;
   the latter two are fixed, but z is merely a *candidate* for the function type
   we are trying to construct.

   We also have the application, a mapping. How do we incorporate this mapping
   into our pattern?  If we were allowed to look inside objects, we could pair a
   function f (an element of the proposed function type z) with an argument x (an
   element of a) and map it to f x (the application of f to x, which inhabits b).

   But instead of dealing with individual pairs (f, x), we can talk about the
   whole *product* of the function type z and argument type a. The product z × a
   is an object, and we can pick as our application morphism an arrow g from that
   object to b. In Set, g would be the function that maps every pair (f, x) to f x.

           _______
     ---  |       |               ___
    | z | | z × a |  ---- g ---> | b |
     ---  |       |               ---
           -------
             ---
            | a |
             ---

   The pattern: a product of two objects z, a, connected to another object b by a
   morphism g.

   Is this pattern specific enough to single out the function type using a
   universal construction? Not in every category, but in the categories of
   interest to us it is. And another question: Would it be possible to define a
   function object without first defining a product? There are categories in which
   there is no product, or there isn't a product for all pairs of objects. The
   answer is no: there is no function type, if there is no product type.

                 NO PRODUCT TYPE  ⇒  NO FUNCTION TYPE.

   Let's review the universal construction... we decree that z together with the
   morphism g from z × a to b is *better* than some other z' with its own
   application g', if and only if there is a unique mapping h from z' to z such
   that the application of g' factors through the application of g.

   The third part of the universal construction is selecting the object that is
   universally the best. Let's call this object a → b.  This object comes with its
   own application---a morphism from a ⇒ b × a to b--- which we will call eval.
   The object a ⇒ b is the best if any other candidate for a function object z'
   can be uniquely mapped to a ⇒ b in such a way that z's application morphism g
   factorizes through eval. The object a ⇒ b with eval is better than any other
   object z' and morphism g.



                _______
     ---       |       |
    | z |      | z × a |__
     ---       |       |  -- g __
      |         -------          \
      |            |              ↘ ---
      h          h × id            | b |
      |            |              ↗ ---
      |      _____ ↓ _____       /
   -- ↓ --  |             |  eval
  | a ⇒ b | | (a ⇒ b) × a |_/
   -------  |             |
             -------------
                  ---
                 | a |
                  ---

   A *function object* from a to b is an object a ⇒ b together with the morphism

                  eval : ((a ⇒ b) × a) → b

    such that for any other object z with a morphism g : z × a → b,

                  ∃! h : z → (a ⇒ b)

    that factors g through eval:

                  g = eval ∘ (h × id).

   (We prove existence of such h below, after we define the "curry" and
   "factorizer" functions.)
                                                                                 -}


{- 9.2 Currying ------------------------------------------------------------------}
{- a → (b → c)                                                       [snippet01] -}

{- a → b → c                                                         [snippet02] -}

{-                                                                   [snippet03] -}
catstr : String → String → String
catstr s s' = s ++ s'

{-                                                                   [snippet04] -}
catstr' : String → String → String
catstr' s = λ s' → s ++ s'

{-                                                                   [snippet05] -}
greet : String → String
greet = catstr "Hello "

{- a × b → c                                                         [snippet06] -}

{-                                                                   [snippet07] -}
curry : (a × b → c) → a → b → c
curry f a b = f (a , b)

{-                                                                   [snippet08] -}
uncurry : (a → b → c) → a × b → c
uncurry f (a , b) = f a b

{-                                                                   [snippet09] -}
factorizer : (a × b → c) → a → (b → c)
factorizer g = λ x → λ y → g (x , y)


{- Existence of morphism h in universal property of function type ----------------}
{-                                                                   [snippet13] -}
eval : ((a → b) × a) → b
eval (f , a) = f a

→-univ-prop-existence' :  ∀ (z : Set)(g : z × a → b)
  →                      Σ[ h ∈ (z → (a → b)) ]  g ≡ eval ∘ h ⟨∘⟩ id

→-univ-prop-existence' z g = factorizer g , refl
{---------------------------------------------------------------------------------}


{- 9.3 Exponentials --------------------------------------------------------------}


{- 9.4 Cartesian Closed Categories -----------------------------------------------}
{- A category is called a "Cartesian closed category" provided it contains

+ a terminal object,
+ a product of every pair of objects,
+ an exponential for every pair of objects.

What's interesting about Cartesian closed categories from the perspective of
computer science is that they provide models for the simply typed lambda calculus,
which forms the basis of all typed programming languages.

The terminal object and the product have their duals: the initial object and the
coproduct.  A Cartesian closed category that also supports those two, and in which
product can be distributed over coproduct

  a × (b + c) = (a × b) + (a × c)
  (b + c) × a = (b × a) + (c × a)

is called a "bicartesian closed category."  We'll see in the next section that
bicartesian closed categories have some interesting properties.
                                                                                 -}

{- 9.5 Exponentials and Algebraic Data Types -------------------------------------}
data Either (a b : Set) : Set where
  Left  : a → Either a b
  Right : b → Either a b

-- Define a boolean version of less than for ℤ, as is done in the standard
-- library for weak inequality, _≤ᵇ_.
open import Agda.Builtin.Int public
  using () renaming ( Int     to ℤ
                    ; pos     to +_        -- "+ n"      stands for "n"
                    ; negsuc  to -[1+_] )  -- "-[1+ n ]" stands for "- (1 + n)"

_<ᵇ_ : ℤ → ℤ → Bool
-[1+ m ] <ᵇ -[1+ n ] = n ℕ.<ᵇ m
(+ m)    <ᵇ -[1+ n ] = false
-[1+ m ] <ᵇ (+ n)    = true
(+ m)    <ᵇ (+ n)    = m ℕ.<ᵇ n

{-                                                                   [snippet10] -}
f : Either ℤ Float → String

{-                                                                   [snippet11] -}
f (Left n) = if (n <ᵇ 0ℤ) then "Negative Int" else "Nonnegative Int"
f (Right n) = if (n <ᶠᵇ 0.0) then "Negative Float" else "Nonnegative Float"

{- 9.6 Curry-Howard Isomorphism --------------------------------------------------}
{- _ : Either a b → a                                                [snippet14] -}

{- absurd : ⊥ → a                                                    [snippet15] -}
absurd : ⊥ → a
absurd ()
