let ( >=> ) = fun m1 m2 ->
  let y, s1 = m1 x in
  let z, s2 = m2 x in
    z, StringLabels.concat +sep:"" [ s1; s2 ]
