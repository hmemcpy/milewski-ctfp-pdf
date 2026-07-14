module Const_Functor (T : T) : Functor = struct
  type 'a t = (T.t, 'a) const

  let fmap _ (Const c) = Const c
end
