sealed trait Expr
case object RZero extends Expr
case object ROne extends Expr
case class RAdd(e1: Expr, e2: Expr) extends Expr
case class RMul(e1: Expr, e2: Expr) extends Expr
case class RNeg(e: Expr) extends Expr