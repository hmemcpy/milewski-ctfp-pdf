let fmapO = Option_Functor.fmap
let fmapL = List_Functor.fmap

let mis2 = (fmapO % fmapL) square mis
