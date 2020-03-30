module Exp_Sum_Impl: Exponential_Of_Sums_Example = {
  let f =
    fun
    | Left(n) => n < 0 ? "Negative int" : "Positive int"
    | Right(x) => x < 0.0 ? "Negative double" : "Positive double"
};
