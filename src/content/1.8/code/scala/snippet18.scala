// return is a keyword in Scala
def pure[A](x: A): Writer[A] = (x, "")