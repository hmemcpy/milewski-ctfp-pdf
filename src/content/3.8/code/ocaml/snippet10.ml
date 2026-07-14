module Fixpoint (F : Functor) = struct
  type 'a t = Fix of 'a t F.t
end
