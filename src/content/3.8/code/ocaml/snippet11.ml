module Fix (F : Functor) = struct
  type 'a fix = In of 'a fix F.t
end
