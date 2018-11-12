def square: Int => Int = x => x * x

val mis: Option[List[Int]] =
  Some(Cons(1, Cons(2, Cons(3, Nil))))

val mis2 = optionFunctor.
  fmap(listFunctor.fmap(square))(mis)