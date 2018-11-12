sealed trait Fix[F[_]]
final case class In[F[_]](f: F[Fix[F]])