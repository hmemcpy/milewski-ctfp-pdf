let f' f = function
  | None -> None
  | Some x -> Some (f x)
;;
