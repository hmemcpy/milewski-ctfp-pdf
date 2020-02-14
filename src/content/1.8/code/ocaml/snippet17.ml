module KleisliComposition = struct
  let ( >=> )
      : ('a -> 'b writer) -> ('b -> 'c writer) -> 'a -> 'c writer
    =
   fun m1 m2 x ->
    let y, s1 = m1 x in
    let z, s2 = m2 y in
    z, StringLabels.concat ~sep:"" [ s1; s2 ]
 ;;
end
