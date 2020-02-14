let rec sum_s n (Cons (x, xs)) =
  if n <= 0 then 0 else x + sum_s (n - 1) (Lazy.force xs)
;;
