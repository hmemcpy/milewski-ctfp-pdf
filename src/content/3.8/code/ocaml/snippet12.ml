module Fixpoint (F : Functor) = struct
  type 'a t = Fix of 'a t F.t

  let fix (f : 'a t F.t) : 'a t = Fix f
end
