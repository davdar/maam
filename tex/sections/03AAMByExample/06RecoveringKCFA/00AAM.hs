data kCFA_AAM = kCFA_AAM Int
instance AAM kCFA_AAM where
  type Time kCFA_AAM = [Call]
  type Addr kCFA_AAM = (Name, [Call])
  tzero (kCFA_AAM k) = []
  tick (kCFA_AAM k) c t = take k (c:t)
  alloc (kCFA_AAM k) x t = (x, t)

