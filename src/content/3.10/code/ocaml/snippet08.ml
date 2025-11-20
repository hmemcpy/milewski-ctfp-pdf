module Pi (P : Profunctor) = struct
  type rank2_p = { p : 'a. ('a, 'a) P.t }

  let pi (e : rank2_p) : ('c, 'c) P.t = e.p
end
