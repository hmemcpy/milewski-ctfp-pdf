module Fix (F : Functor) = struct
  type 'a fix = Fix of 'a fix F.t

  let fix : 'a fix F.t -> 'a fix = fun f -> Fix f
end
