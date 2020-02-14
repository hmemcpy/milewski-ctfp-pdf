let (>>=) ra k = Reader (fun e -> 
  let a = run_reader ra e in
  ...)
