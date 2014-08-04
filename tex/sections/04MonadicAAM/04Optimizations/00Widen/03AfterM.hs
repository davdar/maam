type A_Widen_M d aam = StateT (E aam) (StateT (T aam) (NondetT (State (S d aam))))
