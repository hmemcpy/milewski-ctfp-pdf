{- Chapter 10. Natural Transformations -------------------------------------------}

module Section110 where

open import Agda.Builtin.Int using (Int; pos)
open import Data.Integer using (0ℤ; 1ℤ; _+_)
open import Data.Bool using (Bool; if_then_else_)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Instances using ()
open import Data.Maybe using (Maybe)
open import Data.Maybe.Instances using ()
open import Data.Unit using (⊤; tt)
open import Effect.Functor using (RawFunctor)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open List
open Maybe
{- Functors are mappings between categories that preserve structure.

A functor embeds one category in another. It may collapse multiple things into
one, but it never breaks connections. One way of thinking about it is that with a
functor we are modeling one category inside another. The source category serves as
a model, a blueprint, for some structure that's part of the target category.

There may be many ways of embedding one category in another. Sometimes they are
equivalent, sometimes very different. One may collapse the whole source category
into one object, another may map every object to a different object and every
morphism to a different morphism. The same blueprint may be realized in many
different ways. Natural transformations help us compare these realizations. They
are mappings of functors---special mappings that preserve their functorial nature.

      NATURAL TRANSFORMATIONS ARE MAPPINGS OF FUNCTORS
      THAT PRESERVE THEIR FUNCTORIAL NATURE.

Consider two functors F, G between categories 𝒞 and 𝒟. If you focus on just one
object a ∈ 𝒞ₒ, it is mapped to two objects: F a and G a.  A mapping α : F ⇒ G of
functors, when evaluated at a, should therefore map F a to G a.

Notice that F a and G a are objects in the same category 𝒟. Mappings between
objects in the same category should not be some arbitrary or atificial connections
between objects. It's *natural* to use the existing connections between objects,
namely morphisms.

A *natural transformation*, α : F ⇒ G, is a selection (or "family") of morphisms:
for each object a ∈ 𝒞ₒ, α picks one morphism from F a to G a. This morphism is
called the *component* of α at a (or "along" a) and is sometimes denoted αₐ.

                      α  : F ⇒ G
                    ----------------
                    αₐ : F a → G a
                    αᵤ : F u → G u
                    α̬  : F v → G v
                     ... etc ...

If there is an a ∈ 𝒞ₒ for which no morphism between F a and G a exists in 𝒟, then
there can be no natural transformation between F and G.

Of course that's only half of the story, because functors not only map objects,
they map morphisms as well.  So what does a natural transformation do with those
mappings?  It turns out that the mapping of morphisms is fixed---under any natural
transformation between F and G, F f must be transformed into G f.  What's more,
the mapping of morphisms by the two functors drastically restricts the choices we
have in defining a natural transformation that's compatible with it. Consider a
morphism f : u → v, (u, v ∈ 𝒞ₒ).  It's mapped to two morphisms, F f and G f of 𝒟.

                 F f : F u → F v
                 G f : G u → G v

The natural transformation α : F ⇒ G provides two additional morphisms that
complete the diagram in 𝒟.

                αᵤ : F u → G u
                α̬ : F v → G v

                G ----→ G u
              /        ↗   \
            /         αᵤ     \
          /          /        G f
         u -- F → F u          \
         |           \          ↘
         |        . . \--------→ G v
         f      G      \        ↗
         |    .         F f    /
         |  .            \    α̬
         ↓.               ↘  /
         v ----- F -----→ F v

Now we have two ways of getting from F a to G b. To make sure that they are equal,
we must impose the *naturality condition* that holds for every f:

                G f ∘ αᵤ ≡ α̬  ∘ F f

The naturality condition is a pretty stringent requirement. For instance, if the
morphism F f is invertible, naturality determines α̬  in terms of αᵤ. It
*transports* αᵤ along f:

              α̬  ≡ G f ∘ αᵤ ∘ (F f)⁻¹

If there is more than one invertible morphism between two objects, all these
transports have to agree. In general, though, morphisms are not invertible; but
you can see that the existence of natural transformations between two functors is
far from guaranteed.  So the scarcity or abundance of functors that are related by
natural transformations may tell you a lot about the structure of categories
between which they operate. We'll see some examples of that when we talk about
limits and the Yoneda lemma.

Looking at a natural transformation component-wise, one may say that it maps
objects to morphisms.  Because of the naturality condition, one may also say that
it maps morphisms to commuting squares---there is one commuting naturality square
in 𝒟 for every morphism in 𝒞.
                                                                                 -}

{- 10.1 Polymorphic Functions ----------------------------------------------------}
{- Functors (or, more specifically, endofunctors) in programming correspond to type
constructors that map types to types. They also map functions to functions, and this
mapping is implemented by a higher order function called fmap.

To construct a natural transformation we start with an object (here a type, u).
One functor, F, maps u to the type F u, while another functor, G, maps it to G u.
The component of a natural transformation α at u is a function from F u to G u.

A natural transformation is a polymorphic function defined for all types u.      -}
private variable
  a b c e r : Set
  F G : Set → Set
  f : a → a

module snippet01 where
  α : ∀ a → F a → G a
  α = {!!}

{- The code ∀ a is optional, and we could instead write it using the private
variable a declared above, like this:                                            -}
module snippet02-03 where
  α : F a → G a
  α = {!!}

{- Haskell's parametric polymorphism has an unexpected consequence: every
polymorphic function of the type α : F a → G a, where F and G are functors,
automatically satisfies the naturality condition. Here it is in categorical
notation (f : u → v).

       G f ∘ αᵤ = α̬  ∘ F f

In Haskell, the action of a functor G on a morphism f is implemented using fmap.
I'll first write it in pseudo-Haskell, with explicit type annotations:

       fmapG f ∘ αᵤ = α̬  ∘ fmapF f

Because of type inference, these annotations are not necessary, and the following
equation holds:

       fmap f ∘ α = α̬ ∘ fmap f

This is still not real Haskell---function equality is not expressible in
code---but it's an identity that can be used by the programmer in equational
reasoning; or by the compiler, to implement optimizations.

The reason why the naturality condition is automatic in Haskell has to do with
"theorems for free." Parametric polymorphism, which is used to define natural
transformations in Haskell, imposes very strong limitations on the
implementation---one formula for all types. These limitations translate into
equational theorems about such functions. In the case of functions that transform
functors, free theorems are the naturality conditions.

See the blog post:
https://bartoszmilewski.com/2014/09/22/parametricity-money-for-nothing-and-theorems-for-free/

As mentioned above, one way of thinking about functors in Haskell is to consider
them generalized containers. We can continue this analogy and consider natural
transformations to be recipes for repackaging the contents of one container into
another container. We are not touching the items themselves: we don't modify them,
and we don't create new ones. We are just copying (some of) them, sometimes
multiple times, into a new container.

The naturality condition becomes the statement that it doesn't matter whether we
modify the items first, through the application of fmap, and repackage later; or
repackage first, and then modify the items in the new container, with its own
implementation of fmap. These two actions, repackaging and fmapping, are
orthogonal. "One moves the eggs, the other boils them."

Let's see a few examples of natural transformations in Haskell. The first is
between the list functor, and the Maybe functor. It returns the head of the
list, but only if the list is non-empty:
                                                                     [snippet04] -}
safeHead : List a → Maybe a
safeHead [] = nothing
safeHead (x ∷ xs) = just x

{- It's a function polymorphic in a. It works for any type a, with no limitations,
so it is an example of parametric polymorphism. Therefore it is a natural
transformation between the two functors. But just to convince ourselves, let's
verify the naturality condition.                                                 -}
module snippet05 where
  open RawFunctor ⦃...⦄ renaming (_<$>_ to fmap)
  nc :  ∀{a : Set}{f : a → a}(l : List a)
    →   (fmap f ∘ safeHead) l ≡ (safeHead ∘ fmap f) l
  nc [] = refl
  nc (x ∷ l) = refl

{- We could instead use the syntax convention of the Agda Standard Library which
denotes fmap by _<$>_.                                                           -}
module _ where
  open RawFunctor ⦃...⦄
  nc :  ∀{a : Set}{f : a → a}(l : List a)
    →   (f <$> safeHead l) ≡ safeHead (f <$> l)
  nc [] = refl
  nc (x ∷ l) = refl

{- We have two cases to consider; an empty list:
   fmap f (safeHead []) = fmap f nothing = nothing                   [snippet06]
   safeHead (fmap f []) = safeHead [] = nothing                      [snippet07]
and a non-empty list:
   fmap f (safeHead (x ∷ xs)) = fmap f (Just x) = Just (f x)         [snippet08]
   safeHead (fmap f (x ∷ xs)) = safeHead (f x ∷ fmap f xs) = Just (f x)
                                                                     [snippet09]
We can implement fmap for lists...                                   [snippet10] -}
module snippet10 where
  fmap : (a → b) → List a → List b
  fmap f [] = []
  fmap f (x ∷ xs) = f x ∷ fmap f xs

{- ...and for Maybe...                                               [snippet11] -}
module snippet11 where
  fmap : (a → b) → Maybe a → Maybe b
  fmap f nothing = nothing
  fmap f (just x) = just (f x)

{- But we could instead import and use the fmaps defined in the Agda Standard
Library, as we did above when we imported RawFunctor, and the Data.List.Instances
and Data.Maybe.Instances modules.                                                -}

record Functor (F : Set → Set) : Set₁ where
  constructor functor
  field fmap : (a → b) → F a → F b
open Functor ⦃...⦄

module snippet12 where
  data Const (c a : Set) : Set where
    const : c → Const c a
  {-                                                                 [snippet13] -}
  unConst : Const c a → c
  unConst (const c) = c

  instance
    constFunctor : Functor (Const c)
    constFunctor .fmap = λ f → λ where (const c) → const c
  {-                                                                 [snippet12] -}
  length : List a → Const Int a
  length [] = const 0ℤ
  length (x ∷ xs) = const (1ℤ + unConst (length xs))

  {- length : List a → Int                                           [snippet14] -}
  {-                                                                 [snippet15] -}
  scam : Const Int a → Maybe a
  scam (const x) = nothing

module Reader where
  {-                                                                 [snippet16] -}
  record Reader (e : Set) (a : Set) : Set where
    constructor reader
    field runReader : e → a
  {-                                                                 [snippet17] -}
  instance
    readerFunctor : Functor (Reader e)
    readerFunctor .fmap f (reader g) = reader (f ∘ g)

  {- Recall, Functor (Reader e) is (a → b) → Reader e a → Reader e b.
  If g : e → a and f : a → b, then (reader g) : Reader e a, and the goal is to
  construct an inhabitant of Reader e b.  To do so, we let the runReader map be
  the function f ∘ g : e → b.                                                    -}

  {- Consider the somewhat trivial unit type ⊤ with one element tt.  The functor
  Reader ⊤ takes any type a and maps it into a function type ⊤ → a.
  This is just a family of functions, each of which picks a single element of type
  a. There are as many such functions as there are elements of type a.           -}

  instance
    readerUnitFunctor : Functor (Reader ⊤)
    readerUnitFunctor .fmap f (reader g) = reader (f ∘ g)

  {- Now let's consider natural transformations from this functor to the Maybe
  functor:                                                           [snippet18] -}
  α : Reader ⊤ a → Maybe a
  {- α (reader _) = nothing                                          [snippet19]
                                                                     [snippet20] -}
  α (reader g) = just (g tt)

{- 10.2 Beyond Naturality --------------------------------------------------------}
{- A parametrically polymorphic function between two functors (including the edge
case of the Const functor) is always a natural transformation. Since all standard
algebraic data types are functors, any polymorphic function between such types is
a natural transformation.

We also have function types at our disposal, and those are functorial in their
return type. We can use them to build functors (like the Reader functor) and
define natural transformations that are higher-order functions.

However, function types are not covariant in the argument type. They are
*contravariant*. Of course contravariant functors are equivalent to covariant
functors from the opposite category. Polymorphic functions between two
contravariant functors are still natural transformations in the categorical sense,
except that they work on functors from the opposite category to Haskell types.

Remember the example of a contravariant functor we looked at before:             -}
record Contravariant (F : Set → Set) : Set₁ where
  constructor contravariant
  field contramap : (b → a) → (F a -> F b)
open Contravariant ⦃...⦄

module Op where
  {-                                                                 [snippet21] -}
  record Op (r : Set)(a : Set) : Set where
    constructor op
    field runOp : a → r
  {- This functor is contravariant in a:                             [snippet22] -}
  instance
    opContra : Contravariant (Op r)
    opContra .contramap f (op g) = op (g ∘ f)
  {- Contravariant (Op r) is (b → a) → (Op r a → Op r b).                -}
  {- We can write a polymorphic function from, say, Op Bool to Op String:        -}
  predToStr : Op Bool a → Op String a
  {-                                                                 [snippet23] -}
  predToStr (op f) = op λ x → if (f x) then "T" else "F"
  {- But since the two functors are not covariant, this is not a natural
  transformation in Hask. However, because they are both contravariant, they
  satisfy the "opposite" naturality condition:                       [snippet24] -}
  _ : {f : b → a} → contramap f ∘ predToStr ≡ predToStr ∘ (contramap f)
  _ = refl

{- 10.3 Functor Category ---------------------------------------------------------}
{- Let's take a natural transformation α from functor F to functor G. Its component
at object u is some morphism: αᵤ : F u → G u.

We'd like to compose α with β : G ⇒ H (a nat trans from G to H). The component of
β at u is a morphism: βᵤ : G u → H u.

These morphisms are composable and their composition is another morphism,

                    βᵤ ∘ αᵤ : F a → H a.

We will use this morphism as the component of the natural transformation β ∘ α,
which is the composition of the two natural transformations β and α,

                    (β ∘ α)ᵤ = βᵤ ∘ αᵤ.

             F u ____
            ↗  \     \
           /    αᵤ     \
          F      \      \
         /        ↘      \
        u ------→ G u  (β ∘ α)ᵤ
         \        ↗      /
          H      /      /
           \    βᵤ     /
            ↘  /     /
            H u ←----
                                                                                 -}

{- 10.4 2-Categories -------------------------------------------------------------}
{- 10.5 Conclusion ---------------------------------------------------------------}

{- 10.6 Challenges ---------------------------------------------------------------}

{- 1. Define a natural transformation from the Maybe functor to the list functor.
      Prove the naturality condition for it.                                     -}

{- 2. Define at least two different natural transformations between Reader ()
      and the list functor. How many different lists of () are there?            -}

{- 3. Continue the previous exercise with Reader Bool and Maybe.                 -}

{- 4. Show that horizontal composition of natural transformation satisfies the
      naturality condition (hint: use components). It's a good exercise in
      diagram chasing.                                                           -}

{- 5. Write a short essay about how you may enjoy writing down the evident
      diagrams needed to prove the interchange law.                              -}

{- 6. Create a few test cases for the opposite naturality condition of
      transformations between different Op functors. Here's one choice:

      op : Op Bool Int
      op = Op (λ x → x > 0)

      f : String → Int
      f x = read x
                                                                                 -}
