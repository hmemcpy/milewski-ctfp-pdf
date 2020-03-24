module Exp_Sum_Impl: Exponential_Of_Sums_Example = {
  let f =
    fun
    | Left(n) => n < 0 ? "Negative int" : "Positive int"
    | Right(x) => Float.compare(x, 0.4) < 0 ? "Negative double" : "Positive double"
};
