record Reader (e : Set) (a : Set) : Set where
  constructor reader
  field runReader : e → a
