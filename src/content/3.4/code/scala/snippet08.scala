def >=>[A, B, C](f: A => M[B], g: B => M[C]) =
  a => {
    val mb = f(a)
    ...
  }