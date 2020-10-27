lemma test (h : true) : true → true :=
λ h, trivial

lemma test' (h : 0 = 0) : true → true :=
λ h, trivial

meta def mk_test : tactic unit :=
do
  e ← tactic.to_expr ``(test trivial),
  tactic.to_expr ``(%%e trivial) >>= tactic.exact

meta def mk_test' : tactic unit :=
do
  e ← tactic.to_expr ``(test' rfl),
  tactic.to_expr ``(%%e trivial) >>= tactic.exact

lemma a : true :=
by mk_test

lemma a' : true :=
by mk_test'
