def =>=[E, A, B, C]: (Product[E, A] => B) => (Product[E, B] => C) =>
    (Product[E, A] => C) = f => g => {
  case Product((e, a)) =>
    val b = f(Product((e, a)))
    val c = g(Product((e, b)))
    c
  }
