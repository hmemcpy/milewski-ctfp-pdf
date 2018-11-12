def evalZ: Algebra[RingF, Int] = {
  case RZero => 0
  case ROne => 1
  case RAdd(m, n) => m + n
  case RMul(m, n) => m * n
  case RNeg(n) => -n
}