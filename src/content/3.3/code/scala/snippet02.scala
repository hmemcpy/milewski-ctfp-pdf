def toNat: List[Unit] => Int =
  _.length

def toLst: Int => List[Unit] =
  n => List.fill(n)(())