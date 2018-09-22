data Expr = RZero 
          | ROne
          | RAdd Expr Expr
          | RMul Expr Expr
          | RNeg Expr