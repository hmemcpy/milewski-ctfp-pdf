object Monoid {
  implicit val stringMonoid: Monoid[String] = new Monoid[String] {
    def combine(m1: String, m2: String): String = m1 + m2
    def empty: String = ""
  }
}