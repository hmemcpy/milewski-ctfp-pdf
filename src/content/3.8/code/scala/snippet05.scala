sealed trait Expr
case object RZero extends Expr
case object ROne extends Expr
final case class RAdd(e1: Expr, e2: Expr) extends Expr
final case class RMul(e1: Expr, e2: Expr) extends Expr
final case class RNeg(e: Expr) extends Expr