class AAM aam where
  type Addr (aam :: *) :: *
  type Time (aam :: *) :: *
  tzero :: aam -> Time aam
  tick :: aam -> Call -> Time aam -> Time aam
  alloc :: aam -> Name -> Time aam -> Addr aam
class Delta d where
  type Val (d :: *) :: * -> *
  lit :: d -> Lit -> Val d aam
  clo :: d -> [Name] -> Call -> Env aam -> Val d aam
  op :: d -> Op -> Val d aam -> Maybe (Val d aam)
  elimBool :: d -> Val d aam -> Set Bool
  elimClo :: d -> Val d aam -> Set ([Name], Call, Env aam)
type Env aam = Map Name (Addr aam)
type Store d aam = Map (Addr aam) (Set (Val d aam))
type StateSpace d aam = Set (Call, Env aam, Store d aam, Time aam)
