sa >>= k = State (\s -> let (a, s') = runState sa s
                            sb = k a 
                        in runState sb s')