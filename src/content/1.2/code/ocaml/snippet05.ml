let fact n = Seq.(fold_left ( * ) 1 (take n (ints 1)))
