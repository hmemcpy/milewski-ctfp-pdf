// Read more about foldMap:
// typelevel.org/cats/typeclasses/foldable.html
def foldMap[F[_], A, B](fa: F[A])(f: A => B)
                       (implicit B: Monoid[B]): B = ???
implicit def listMonoid[A]: Monoid[List[A]] = ???

def toLst[A]: List[A] => Lst[A] = as => new Lst[A] {
  def apply(): `PolyFunctionM`[aTo, Id] =
    new `PolyFunctionM`[aTo, Id] {
      def apply[I: Monoid](fa: aTo[I]): Id[I] =
        foldMap(as)(fa)
    }
}

def fromLst[A]: Lst[A] => List[A] =
  f => f().apply(a => List(a))