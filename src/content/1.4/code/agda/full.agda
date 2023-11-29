open import Data.Char using (Char; toUpper)
open import Data.String using (String; _++_; fromList; toList; words)
open import Data.Product using (_×_; _,_) renaming (proj₁ to fst; proj₂ to snd)
open import Data.List using (List) renaming (map to lmap)
open import Function using (_∘_; _$_)

private variable a b c : Set

Writer : Set → Set
Writer a = a × String

morphism : a → Writer b
morphism = {!!}

_>=>_ : (a → Writer b) → (b → Writer c) → (a → Writer c)
m1 >=> m2 = λ x →
  let (y , s1) = m1 x
      (z , s2) = m2 y
  in (z , s1 ++ s2)

map : (Char → Char) → String → String
map f = fromList ∘ lmap f ∘ toList

return : a → Writer a
return x = (x , "")

upCase : String → Writer String
upCase s = ( map toUpper s , "upCase " )

toWords : String → Writer (List String)
toWords s = ( words s , "toWords " )

process : String → Writer (List String)
process = upCase >=> toWords
