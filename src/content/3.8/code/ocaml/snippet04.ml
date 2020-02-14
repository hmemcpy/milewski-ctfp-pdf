module Ring = struct
  module RingAlg = Algebra (struct
    type 'a f = 'a ring_f
  end)

  let eval_z : 'a RingAlg.algebra = function
    | RZero -> 0
    | ROne -> 1
    | RAdd (m, n) -> m + n
    | RMul (m, n) -> m * n
    | RNeg n -> -n
  ;;
end
