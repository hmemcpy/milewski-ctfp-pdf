trait Procompose[Q[_, _], P[_, _], A, B]

object Procompose{
  def apply[Q[_, _], P[_, _], A, B, C]
      (qac: Q[A, C])(pcb: P[C, B]): Procompose[Q, P, A, B] = ???
}