execSymkCFA :: Int -> Call -> SS (A_M Sym_Delta ZCFA_AAM) Call
execSymkCFA k = exec Sym_Delta (kCFA_AAM k)
