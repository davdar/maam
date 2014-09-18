type Env = Map Name Val
data Val = LitV Lit | Clo [Name] Call Env
type StateSpace = Maybe (Call, Env)
