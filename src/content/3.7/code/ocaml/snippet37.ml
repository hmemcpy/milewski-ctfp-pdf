module StoreComonadBase (S : sig
  type s
end)
(F : Functor with type 'a t = (S.s, 'a) store) :
  ComonadBase with type 'a w = (S.s, 'a) store = struct
  type 'a w = (S.s, 'a) store

  include F

  let extract (Store (f, s)) = f s
end

module StoreComonadDuplicate (S : sig
  type s
end) : ComonadDuplicate with type 'a w = (S.s, 'a) store = struct
  type 'a w = (S.s, 'a) store

  let duplicate (Store (f, s)) = Store (make_store f, s)
end

(* Generate Full comonad *)
module StoreComonad (S : sig
  type s
end)
(F : Functor with type 'a t = (S.s, 'a) store) :
  Comonad with type 'a w = (S.s, 'a) store =
  ComonadImplViaExtend
    (StoreComonadBase (S) (F)) (StoreComonadDuplicate (S))
