def fst[I]: ((I, _)) => I = _._1

def toExp[A, B]: (A => B) => Exp[A, B] = f => new Lan[(A, ?), I, B] {
  def fk[L](ki: (A, L)): B =
    f.compose(fst[A])(ki)

  def di[L]: I[L] = I()
}

def fromExp[A, B]: Exp[A, B] => (A => B) =
  lan => a => lan.fk((a, lan.di))