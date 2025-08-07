let guard b =
  if b then Seq.return () (* Analogous to [()] *)
  else Seq.empty (* Analogous to [] *)
