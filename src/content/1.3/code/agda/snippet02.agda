instance
  StringMonoid : Monoid String
  StringMonoid = record
    { mempty = ""
    ; mappend = _++_
    }
