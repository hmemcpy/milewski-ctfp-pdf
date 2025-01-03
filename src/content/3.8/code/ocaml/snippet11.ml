module Fixpoint (F : Functor) = struct
  type 'a t = In of 'a t F.t
end
