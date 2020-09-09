let fmapO = Option_Functor.fmap;
let fmapL = List_Functor.fmap;
let fmapC = (f, l) => (compose(fmapO, fmapL))(f, l);
let mis2 = fmapC(square, mis);
