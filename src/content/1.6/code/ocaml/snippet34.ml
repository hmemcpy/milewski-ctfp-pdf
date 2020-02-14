let prod_to_sum (x, e) =
  match e with
  | Left y -> Left (x, y)
  | Right z -> Right (x, z)
;;
