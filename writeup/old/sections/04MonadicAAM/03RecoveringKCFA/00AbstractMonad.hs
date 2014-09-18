type A_M d aam = StateT (E aam) (StateT (S d aam) (StateT (T aam) Nondet))

