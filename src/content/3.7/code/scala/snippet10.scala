def extract[E, A]: Product[E, A] => A = {
  case Product((e, a)) => a
}