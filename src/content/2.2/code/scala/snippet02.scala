def contramap[C, C1, D[_]](f: C1 => C, u: C => Lim[D]): (C1 => Lim[D]) =
  u compose f