let ( >>= ) sa k =
  State
    (fun s ->
      let a, s' = run_state sa s in
      let sb = k a in
      run_state sb s')
