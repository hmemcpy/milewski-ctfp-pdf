startsWithSymbol : String × String × Int → Bool
startsWithSymbol (name , symbol , _) = isPrefixOf symbol name
-- There's no `isPrefixOf` function in the Agda standard library...
-- [Agda's Not Haskell!]
-- ...but we can define our own, as follows:
isPrefixOf : String → String → Bool
isPrefixOf s s' = isPrefix-Chars (toList s) (toList s')
  where
  isPrefix-Chars : List Char → List Char → Bool
  isPrefix-Chars _ [] = true
  isPrefix-Chars [] _ = false
  isPrefix-Chars (x ∷ xs) (y ∷ ys) = (x ≈ᵇ y) ∧ isPrefix-Chars xs ys
