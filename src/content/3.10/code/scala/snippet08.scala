// no Rank-N types in Scala
// need a higher rank polymorphic function
trait PolyFunction2[P[_, _]] {
  def apply[C](in: PolyFunction1[P]): P[C, C]
}

def pi[P[_, _]](implicit P: Profunctor[P]): PolyFunction2[P] =
  new PolyFunction2[P] {
    def apply[C](in: PolyFunction1[P]): P[C, C] =
      in()
  }