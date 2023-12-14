f (Left n) = if (n <ᵇ 0ℤ) then "Negative Int" else "Nonnegative Int"
f (Right n) = if (n <ᶠᵇ 0.0) then "Negative Float" else "Nonnegative Float"
