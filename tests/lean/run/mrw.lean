example (n : nat) : ∃ x, x + n = n + 1 :=
begin
  constructor,
  fail_if_success {rw [nat.zero_add] {unify := ff}},
  rw [nat.add_comm]
end
