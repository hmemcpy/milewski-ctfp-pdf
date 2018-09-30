evalZ :: Expr -> Integer
evalZ RZero        = 0
evalZ ROne         = 1
evalZ (RAdd e1 e2) = evalZ e1 + evalZ e2
evalZ (RMul e1 e2) = evalZ e1 * evalZ e2
evalZ (RNeg e)     = -(evalZ e)