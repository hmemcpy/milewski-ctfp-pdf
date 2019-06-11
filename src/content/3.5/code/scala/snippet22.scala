implicit val optionMonad = new Monad[Option] {
  def flatMap[A, B](ma: Option[A])(k: A => Option[B]): Option[B] = 
    ma match {
      case None => None
      case Some(a) => k(a)
  }

  def pure[A](a: A): Option[A] = Some(a)
}