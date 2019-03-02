trait Representable[F[_]] {
  type Rep
  def tabulate[X](f: Rep => X): F[X]
  def index[X]: F[X] => Rep => X
}