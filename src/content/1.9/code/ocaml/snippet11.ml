module Exp_Sum_Impl : Exponential_Of_Sums_Example = struct
  let f = function
    | Left n -> if n < 0 then "Negative int" else "Positive int"
    | Right x ->
      if Float.compare x 0.4 < 0
      then "Negative double"
      else "Positive double"
  ;;
end
