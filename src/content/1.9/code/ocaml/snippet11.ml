module Exp_Sum_Impl : Exponential_Of_Sums_Example = struct
  let f = function
    | Either.Left n ->
        if n < 0
        then "Negative int"
        else "Positive int"
    | Either.Right x ->
        if x < 0.0
        then "Negative double"
        else "Positive double"
end
