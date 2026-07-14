(* OCaml is strict by default, so to prevent hanging due
   to the streams being infinite, we make them lazy. *)
type ('e, 'a) stream_f = StreamF of ('e * 'a Lazy.t)

(* Wrapper for parameterized stream *)
module type Type = sig
  type t
end

(* The stream functor could be thus defined as follows: *)
module Stream_Functor (E : Type) : Functor
with type 'a t = (E.t, 'a) stream_f =
struct
  type 'a t = (E.t, 'a) stream_f

  let fmap f (StreamF (e, a)) = StreamF (e, lazy (f (Lazy.force a)))
end

(* And applied to integers *)
module Stream_Functor_Int = Stream_Functor (Int)
