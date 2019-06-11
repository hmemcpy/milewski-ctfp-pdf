mu.compose(bimap(eta)(identity[M]))(((), x)) == lambda(((), x))

mu.compose(bimap(identity[M])(eta))((x, ())) == rho((x, ()))