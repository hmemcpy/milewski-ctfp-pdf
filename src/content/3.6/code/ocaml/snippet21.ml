module AdjunctionState (S : sig
  type s
end)
(F : Functor with type 'a t = (S.s, 'a) prod)
(R : Representable with type 'a t = (S.s, 'a) reader) : Adjunction =
struct
  type 'a f = (S.s, 'a) prod
  type 'a r = (S.s, 'a) reader

  include F
  include R

  let unit a = Reader (fun s -> Prod (a, s))
  let counit (Prod (Reader f, s)) = f s
end
