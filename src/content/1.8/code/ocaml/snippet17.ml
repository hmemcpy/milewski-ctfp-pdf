module KleisliComposition = struct
  let ( >=> ) (m1 : 'a -> 'b writer) (m2 : 'b -> 'c writer) =
   fun x ->
    let y, s1 = m1 x in
    let z, s2 = m2 y in
    (z, s1 ^ s2)
end
