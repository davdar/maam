type Addr = Integer
type Time = Integer
type Env = Map Name Addr
type Store = Map Addr Val
data Val = LitV Lit | Clo [Name] Call Env
type StateSpace = Maybe (Call, Env, Store, Time)
