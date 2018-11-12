trait Profunctor[P[_, _]] {
  def dimap[A, B, C, D]
      (f: C => A)(g: B => D)(pab: P[A, B]): P[C, D]
}