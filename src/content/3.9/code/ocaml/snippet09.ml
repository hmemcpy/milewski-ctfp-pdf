module Store_Functor (S : sig
  type s
end) : Functor with type 'a t = (S.s, 'a) store = struct
  type 'a w = (S.s, 'a) store
  type 'a t = 'a w

  let fmap g (Store (f, s)) = Store (compose g f, s)
end
