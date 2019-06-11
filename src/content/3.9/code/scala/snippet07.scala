case class Store[S, A](run: S => A, s: S)

// convenient partially applied constructor
object Store {
  def apply[S, A](run: S => A): S => Store[S, A] =
    s => new Store(run, s)
}