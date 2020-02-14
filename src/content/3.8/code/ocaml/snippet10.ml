module Fix (F : Functor) = struct
  type 'a fix = Fix of 'a fix F.t
end
