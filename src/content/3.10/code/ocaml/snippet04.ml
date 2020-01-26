(* There is no compose operator in OCaml *)

;;
compose (dimap id f) alpha = compose (dimap f id) alpha
