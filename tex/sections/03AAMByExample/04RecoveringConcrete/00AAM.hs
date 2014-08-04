data C_AAM = C_AAM
instance AAM C_AAM where
  type Time C_AAM = Integer
  type Addr C_AAM = (Integer, Name)
  tzero C_AAM = 0
  tick C_AAM _ t = t+1
  alloc C_AAM x t = (t, x)
