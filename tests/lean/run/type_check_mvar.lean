open tactic

example : true := by do
eq ← mk_const ``eq,
ty ← mk_meta_univ >>= mk_meta_var ∘ expr.sort,
let zero := `(0 : ℕ),
let e := eq ty zero zero,
success_if_fail $ type_check e,
triv
