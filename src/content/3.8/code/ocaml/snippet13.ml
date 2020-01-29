module Fix (F : Functor) = struct
  type 'a fix = Fix of 'a fix F.t

  let unfix : 'a fix -> 'a fix F.t = fun (Fix f) -> f
end
