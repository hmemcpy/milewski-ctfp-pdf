def tail[A]: Stream[A] => Stream[A] = {
  case Stream(a, as) => as()
}