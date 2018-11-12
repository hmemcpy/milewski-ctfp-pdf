def swap[A, B]: ((A, B)) => (B, A) = {
  case (x, y) => (y, x)
}