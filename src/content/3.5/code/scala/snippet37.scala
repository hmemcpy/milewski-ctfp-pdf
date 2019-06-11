def main: IO[Unit] = for {
  _ <- putStr("Hello ")
  _ <- putStr("World!")
} yield ()