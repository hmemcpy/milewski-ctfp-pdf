def =>=[W[_], A, B, C]
    : (W[A] => B) =>
      (W[B] => C) =>
      (W[A] => C) = f => g => {
  g compose extend(f)
}