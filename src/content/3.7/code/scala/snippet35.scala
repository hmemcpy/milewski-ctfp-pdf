object Store {
  def apply[S, A](run: S => A): S => Store[S, A] =
    s => new Store(run, s)
}