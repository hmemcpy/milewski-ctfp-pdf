def alphaInv[A, B, C]: ((A, (B, C))) => (((A, B), C)) = {
  case (x, (y, z)) => ((x, y), z)
}