movingAvg :: Fractional a => Int -> Stream a -> Stream a
movingAvg n = extend (average n)