let pred_to_str (Op f) = Op (fun x -> if f x then "T" else "F")
