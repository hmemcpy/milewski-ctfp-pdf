module StreamRepresentable : Representable = struct
  type rep = int
  type 'x t = 'x stream

  let rec tabulate f = Cons (f 0, lazy (tabulate (compose f succ)))

  let rec index (Cons (b, bs)) n =
    if n = 0 then b else index (Lazy.force bs) (n - 1)
  ;;
end
