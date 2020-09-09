/* List module in the OCaml standard library accepts list before z */
List.fold_right(f, [x], z) == f(x, z);
