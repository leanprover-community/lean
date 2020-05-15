open tactic
#eval mk_instance `(inhabited ℕ)
local attribute [-instance] nat.inhabited
#eval success_if_fail $ mk_instance `(inhabited ℕ)