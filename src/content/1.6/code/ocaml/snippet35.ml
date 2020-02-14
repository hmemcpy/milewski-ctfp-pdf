let sum_to_prod = function
  | Left (x, y) -> x, Left y
  | Right (x, z) -> x, Right z
;;
