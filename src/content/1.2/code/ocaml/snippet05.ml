let fact n = List.fold (List.range 1 n) ~init:1 ~f:( * )
