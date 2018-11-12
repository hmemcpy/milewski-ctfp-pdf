trait Comonoid[M] {
  def split(x: M): (M, M)
  def destroy(x: M): Unit
}