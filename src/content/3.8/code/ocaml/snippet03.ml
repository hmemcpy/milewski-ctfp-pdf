type 'a ring_f =
  | RZero
  | ROne
  | RAdd of ('a * 'a)
  | RMul of ('a * 'a)
  | RNeg of 'a
