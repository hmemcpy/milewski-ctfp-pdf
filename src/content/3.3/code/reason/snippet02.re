let to_nat: list(unit) => int = List.length;
let to_lst: int => list(unit) = n => List.init(n, ~f=_ => ());
