def alpha: (Int => ?) ~> List = new ~>[Int => ?, List] {
  def apply[A](fa: Int => A) =
    List(12).map(fa)
}