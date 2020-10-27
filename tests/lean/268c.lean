def nat.case {α} (a b : α) (n : ℕ) : α := nat.cases_on n a (λ _, b)

variables (a b c : ℕ)
#check nat.case a b c -- a.case b c : ℕ
set_option pp.generalized_field_notation false
#check a.case b c -- nat.case b c a : ℕ
