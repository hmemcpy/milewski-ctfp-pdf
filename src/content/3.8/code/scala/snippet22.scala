def length[E](l: List[E]): Int =
  l.foldRight(0)((e, n) => n + 1)