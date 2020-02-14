let ( =>= ) f g (P (e, a)) =
  let b = f (P (e, a)) in
  let c = g (P (e, b)) in
  c
;;
