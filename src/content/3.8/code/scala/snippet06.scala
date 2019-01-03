def evalZ: Expr => Int = {
  case RZero => 0
  case ROne => 1
  case RAdd(e1, e2) => evalZ(e1) + evalZ(e2)
  case RMul(e1, e2) => evalZ(e1) * evalZ(e2)
  case RNeg(e) => -evalZ(e)
}