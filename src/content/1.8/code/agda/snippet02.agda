instance
  _ : Bifunctor _×_
  _ = record { bimap = bimap } where
      bimap : (a → c) → (b → d) → a × b → c × d
      bimap a→b c→d (a , c) = a→b a , c→d c
