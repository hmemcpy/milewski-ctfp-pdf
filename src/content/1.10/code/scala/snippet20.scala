def obvious[A]: Reader[Unit, A] => Option[A] = {
  case Reader(g) => Some(g())
}