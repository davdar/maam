execSymkCFA :: Int -> Call -> StateSpace Sym_Delta ZCFA_AAM
execSymkCFA k = exec Sym_Delta (kCFA_AAM k)

