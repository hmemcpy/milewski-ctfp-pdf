def guard: Boolean => List[Unit] = {
  case true => List(())
  case false => List.empty[Unit]
}