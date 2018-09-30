lambda, rho :: Profunctor p => SumP p -> DiagSum p
lambda (SumP f pab) = DiagSum (dimap f id pab)
rho    (SumP f pab) = DiagSum (dimap id f pab)