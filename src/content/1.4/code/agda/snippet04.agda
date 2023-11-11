m1 >=> m2 = λ x ->
  let (y , s1) = m1 x
      (z , s2) = m2 y
  in (z , s1 ++ s2)
