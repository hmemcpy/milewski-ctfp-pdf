data Reader a x : Set where
  reader : (a → x) → Reader a x
