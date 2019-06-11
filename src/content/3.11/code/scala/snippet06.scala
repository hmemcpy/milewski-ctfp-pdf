trait Lan[K[_], +D[_], A] {
  def fk[I](ki: K[I]): A
  def di[I]: D[I]
}