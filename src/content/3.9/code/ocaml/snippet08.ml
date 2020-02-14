module Store_comonad (S : sig
  type s
end)
(F : Functor with type 'a t = (S.s, 'a) store) :
  Comonad with type 'a w = (S.s, 'a) store = struct
  type 'a w = (S.s, 'a) store

  include F

  let extract : 'a w -> 'a = fun (Store (f, s)) -> f s

  let duplicate : 'a w -> 'a w w =
   fun (Store (f, s)) -> Store ((fun s -> Store (f, s)), s)
 ;;
end
