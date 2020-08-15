example (n m k : ℕ) (h : n + 1 = m + 1) : m = k → n = k :=
begin
  injection h with x y z,
  guard_hyp n : ℕ,
  guard_hyp m : ℕ,
  guard_hyp k : ℕ,
  guard_hyp h : n + 1 = m + 1,
  guard_hyp x : n = m,
  guard_target m = k → n = k,
  admit
end
