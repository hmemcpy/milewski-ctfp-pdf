object Monoid {
  implicit def stringMonoid: Monoid[String] = new Monoid[String] {
    def mempty: String = ""
    def mappend(m1: String, m2: String): String = m1 + m2
  }
}