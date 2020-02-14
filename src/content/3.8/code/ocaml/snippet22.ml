let length xs = List.fold_right (fun e n -> n + 1) xs 0
