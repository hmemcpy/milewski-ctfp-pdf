def dumb[A]: Reader[Unit, A] => Option[A] = {
  case Reader(_) => None
}