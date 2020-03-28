type ring_f('a) =
  | RZero
  | ROne
  | RAdd(('a, 'a))
  | RMul(('a, 'a))
  | RNeg('a);
