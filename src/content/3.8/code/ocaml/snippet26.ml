type ('e, 'a) stream_f = StreamF of ('e * 'a)

module Stream_Functor (E : sig
  type e
end) : Functor with type 'a t = (E.e, 'a) stream_f = struct
  type 'a t = (E.e, 'a) stream_f

  let fmap f = function
    | StreamF (e, a) -> StreamF (e, f a)
  ;;
end
