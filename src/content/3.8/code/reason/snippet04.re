module Ring = {
  module RingAlg = Algebra({type f('a) = ring_f('a);});

  let eval_z: RingAlg.algebra('a) = (
    fun
    | RZero => 0
    | ROne => 1
    | RAdd(m, n) => m + n
    | RMul(m, n) => m * n
    | RNeg(n) => - n
  );
};
