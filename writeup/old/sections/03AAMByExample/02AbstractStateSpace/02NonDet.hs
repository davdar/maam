type Store aam = Map (Addr aam) (Set (Val aam))
type StateSpace aam = Set (Call, Env aam, Store aam, Time aam)
