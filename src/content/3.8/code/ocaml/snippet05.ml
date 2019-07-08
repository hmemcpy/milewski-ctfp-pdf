type expr =
  | RZero
  | ROne
  | RAdd of (expr * expr)
  | RMul of (expr * expr)
  | RNeg of expr
