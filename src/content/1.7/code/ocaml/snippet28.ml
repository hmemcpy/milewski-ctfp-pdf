module Const_Functor (T : T) : Functor = struct
  type 'a t = (T.t, 'a) const

  let fmap f (Const c) = Const c (* or even let fmap _ c = c *)
end
