average :: Fractional a => Int -> Stream a -> a
average n stm = (sumS n stm) / (fromIntegral n)