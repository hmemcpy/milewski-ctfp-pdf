let to_nat : unit list -> int = List.length
let to_lst : int -> unit list = fun n -> List.init n ~f:(fun _ -> ())
