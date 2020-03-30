let rec eval_z: expr => int = (
  fun
  | RZero => 0
  | ROne => 1
  | RAdd(e1, e2) => eval_z(e1) + eval_z(e2)
  | RMul(e1, e2) => eval_z(e1) * eval_z(e2)
  | RNeg(e) => - eval_z(e)
);
