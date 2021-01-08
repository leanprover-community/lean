def foo (n : ℕ) : Prop := true

lemma bar (n : ℕ) : foo n := trivial
lemma baz (h : true) : ∀ {n : ℕ} (h' : foo n), true :=
λ a b, trivial

meta def mk_true : tactic unit :=
do
  e ← tactic.to_expr ``(baz trivial),
  tactic.to_expr ``(%%e (bar 2)) >>= tactic.exact

example : true :=
by mk_true

