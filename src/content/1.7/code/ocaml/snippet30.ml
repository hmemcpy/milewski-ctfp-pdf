let square x = x * x
let mis = Some (Cons (1, Cons (2, Cons (3, Nil))))
let mis2 = Option_Functor.fmap (List_Functor.fmap square) mis
