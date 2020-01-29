let pred_to_str = function
  | Op f -> Op (fun x -> if f x then "T" else "F")
;;
