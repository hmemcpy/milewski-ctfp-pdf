module List_C (E : sig
  type e
end) =
struct
  module Stream_F : Functor with type 'a t = (E.e, 'a) stream_f =
    Stream_Functor (E)

  module Cata_Stream = Cata (Stream_F)

  let to_list_c : E.e list Cata_Stream.fix -> E.e list =
   fun s_fix ->
    Cata_Stream.cata (fun (StreamF (e, a)) -> e :: a) s_fix
 ;;
end
