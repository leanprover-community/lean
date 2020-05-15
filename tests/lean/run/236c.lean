constant foo_rec (n : ℕ) (k : Type) [has_one k]  : Prop

lemma stupid (k : Type) [has_one k] (n : ℕ) :
  foo_rec nat.zero k ↔ foo_rec nat.zero k :=
by simp only [nat.nat_zero_eq_zero]

open tactic
#eval do
cgr ← mk_congr_lemma_simp `(foo_rec),
type_check cgr.proof
