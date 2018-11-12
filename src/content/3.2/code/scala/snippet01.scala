def swap[A, B]: ((A, B)) => (B, A) = {
  case (a, b) => (b, a)
}