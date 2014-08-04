data E aam = E aam
type instance Cell (E aam) = Env aam
data S d aam = S d aam
type instance Cell (S d aam) = Store d aam
data T aam = T aam
type instance Cell (T aam) = Time aam
type M d aam = StateT (E aam) (StateT (S d aam) (StateT (T aam) []))
