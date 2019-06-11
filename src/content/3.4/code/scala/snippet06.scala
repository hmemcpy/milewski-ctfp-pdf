def tell[W](s: W): Writer[W, Unit] =
  Writer((), s)