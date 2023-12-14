record Op (r : Set)(a : Set) : Set where
  constructor op
  field runOp : a → r
