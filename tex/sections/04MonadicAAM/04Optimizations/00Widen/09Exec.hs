execSymkCFAWiden :: Int -> Call -> SS (A_Widen_M Sym_Delta ZCFA_AAM) Call
execSymkCFAWiden k = exec Sym_Delta (kCFA_AAM k)

