module AdjunctionState (S : sig
  type s
end) :
  Adjunction with type 'a f = (S.s, 'a) prod
  and type 'a r = (S.s, 'a) reader =
struct
  type 'a f = (S.s, 'a) prod
  type 'a r = (S.s, 'a) reader

  let counit (Prod (Reader f, s)) = f s
  let unit a = Reader (fun s -> Prod (a, s))
end
