let ( >>= ) ra k =
  Reader
    (fun e ->
      let a = run_reader ra e in
      let rb = k a in
      run_reader rb e)
