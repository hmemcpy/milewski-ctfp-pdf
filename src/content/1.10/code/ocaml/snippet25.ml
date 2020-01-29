module Op_Bool = Op_Contravariant (struct
  type r = bool
end)

let op_bool_contramap : ('b -> 'a) -> 'a Op_Bool.t -> 'b Op_Bool.t =
  Op_Bool.contramap
;;
