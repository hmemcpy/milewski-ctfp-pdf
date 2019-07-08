module Pythagorean = struct
  let ( let* ) = Fn.flip Gen.flat_map
  let ( let+ ) x f = Gen.map f x
  let guard b = if b then Gen.return () else Gen.empty

  let triples =
    let* z = Gen.init (fun i -> i + 1) in
    let* x = Gen.init ~limit:z (fun i -> i + 1) in
    let* y = Gen.init ~limit:z (fun i -> i + x) in
    if (x * x) + (y * y) = z * z
    then Gen.return (x, y, z)
    else Gen.empty
end
