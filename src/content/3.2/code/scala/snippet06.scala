def unit[A](a: A): U[F[A]] =
    leftAdjunct(a)(identity)
  
  def counit[A](a: F[U[A]]): A =
    rightAdjunct(a)(identity)
  
  def leftAdjunct[A, B](a: A)(f: F[A] => B): U[B] =
    U.map(unit(a))(f)
  
  def rightAdjunct[A, B](a: F[A])(f: A => U[B]): B =
    counit(F.map(a)(f))