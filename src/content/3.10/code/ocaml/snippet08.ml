module Pi (P : Profunctor) = struct
  type rank2_p = { p : 'a. ('a, 'a) P.p }

  let pi : rank2_p -> ('c, 'c) P.p = fun e -> e.p
end
