module Reader_Functor (T : sig
  type e
end) : Functor with type 'a t = (T.e, 'a) reader = struct
  type 'a t = (T.e, 'a) reader

  let fmap f (Reader g) = Reader (fun e -> f (g e))
end
