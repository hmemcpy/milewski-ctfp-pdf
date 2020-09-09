type expr =
  | RZero
  | ROne
  | RAdd((expr, expr))
  | RMul((expr, expr))
  | RNeg(expr);
