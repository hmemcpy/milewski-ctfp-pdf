let ( >=> ) m1 m2 = fun x ->
  let y, s1 = m1 x in
  let z, s2 = m2 y in
  z, s1 ^ s2
