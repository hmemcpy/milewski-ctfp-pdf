let fmap f = function
  | None -> None
  | Some x -> Some (f x)
;;
