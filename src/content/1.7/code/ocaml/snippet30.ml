let square x = x * x

let mis : int list option = Some [ 1; 2; 3 ]

let mis2 = Option_Functor.fmap (List_Functor.fmap square) mis
