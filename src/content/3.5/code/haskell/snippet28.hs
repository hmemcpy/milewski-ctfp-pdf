runCont ka (\a -> let kb = kab a 
                  in runCont kb hb)