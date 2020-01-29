module Reader_Functor (T : sig
  type e
end) : Functor = struct
  type 'a t = (T.e, 'a) reader

  let fmap : 'a 'b. ('a -> 'b) -> 'a t -> 'b t =
   fun f -> function
    | Reader r -> Reader (compose f r)
 ;;
end
