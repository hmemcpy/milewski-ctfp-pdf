;;
run_cont ka (fun a ->
    let kb = kab a in
    run_cont kb hb)
