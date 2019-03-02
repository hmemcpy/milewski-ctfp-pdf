sealed trait Fix[F[_]]
case class In[F[_]](f: F[Fix[F]])