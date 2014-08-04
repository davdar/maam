data ZCFA_AAM = ZCFA_AAM
instance AAM ZCFA_AAM where
  type Time ZCFA_AAM = ()
  type Addr ZCFA_AAM = Name
  tzero ZCFA_AAM = ()
  tick ZCFA_AAM _ () = ()
  alloc ZCFA_AAM x () = x
