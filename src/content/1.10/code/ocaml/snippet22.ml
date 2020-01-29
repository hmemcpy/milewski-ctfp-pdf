module Op_Contravariant (T : sig
  type r
end) : Contravariant = struct
  type 'a t = (T.r, 'a) op

  let contramap : ('b -> 'a) -> 'a t -> 'b t =
   fun f -> function
    | Op g -> Op (compose g f)
 ;;
end
