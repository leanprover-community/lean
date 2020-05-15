constant foo_rec (n : ℕ) (k : Type) [group k]  : Prop

lemma stupid (k : Type) [group k] (n : ℕ) :
  foo_rec nat.zero k ↔ foo_rec nat.zero k :=
by simp only [nat.nat_zero_eq_zero]

open tactic
#eval do
cgr ← mk_congr_lemma_simp `(foo_rec),
type_check cgr.proof