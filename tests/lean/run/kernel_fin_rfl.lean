example : (1 : fin 2) = (3 : fin 2) := rfl
example : (3/2 : fin 2) = (0 : fin 2) := rfl
example : (1 + 1 + 1 * 1 : fin 2) = (1 : fin 2) := rfl
example : fin.succ 0 = (1 : fin 2) := rfl