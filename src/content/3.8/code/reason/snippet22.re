let length = xs => List.fold_right((e, n) => n + 1, xs, 0);
