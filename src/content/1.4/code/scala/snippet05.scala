def pure[A](x: A): Writer[A] = (x, "")