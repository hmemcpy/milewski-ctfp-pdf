module Pythagorean = {
  let (let*) = Fn.flip(Gen.flat_map);
  let (let+) = (x, f) => Gen.map(f, x);
  let guard = b => b ? Gen.return() ? Gen.empty;

  let triples = {
    let* z = Gen.init(i => i + 1);
    let* x = Gen.init(~limit=z, i => i + 1);
    let* y = Gen.init(~limit=z, i => i + x);
    let+ _ = guard(x * x + y * y == z * z);
    Gen.return((x, y, z));
  };
};
