module EndsEqualizer (P : Profunctor) = struct
  let lambda (paa : ('a, 'a) P.t) (f : 'a -> 'b) : ('a, 'b) P.t =
    P.dimap Fun.id f paa

  let rho (pbb : ('b, 'b) P.t) (f : 'a -> 'b) : ('a, 'b) P.t =
    P.dimap f Fun.id pbb
end
