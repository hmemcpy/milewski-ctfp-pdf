let rec fib = function
  | ZeroF -> 1, 1
  | SuccF (m, n) -> n, m + n
;;
