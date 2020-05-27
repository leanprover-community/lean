-- some space-sensitive tests

#check (- - 2 : int)
universe u
variables (A : Type u) (a b : A) (H : a = b)
lemma symm₂ : b = a := eq.symm H
#check @symm₂ -- double space before type?
run_cmd do
  f1 ← tactic.to_expr ```(@symm₂) >>= tactic.infer_type >>= tactic.pp,
  f2 : format ← pure $ to_fmt "∀ (A : Type ?) (a b : A), a = b → b = a",
  tactic.trace f1,
  guard $ f1.to_string = f2.to_string

constant f : nat → nat
constant g : nat → nat → nat
notation A `:+1`:100000 := f A
set_option pp.notation false
run_cmd do
  f1 ← tactic.to_expr ```(g 0:+1:+1 (1:+1 + 2:+1):+1) >>= tactic.pp, -- additional space in has_add.add (*f 1
  f2 : format ← pure $ to_fmt "g (f (f 0)) (f (has_add.add (f 1) (f 2)))",
  tactic.trace f1,
  guard $ f1.to_string = f2.to_string


set_option pp.beta false
run_cmd do
  f1 ← tactic.to_expr ```(λ {A : Type} {B : Type} (a : A) (b : B), a) >>= tactic.pp,
  f2 : format ← pure $ to_fmt "λ {A B : Type} (a : A) (b : B), a",
  tactic.trace f1,
  guard $ f1.to_string = f2.to_string

set_option pp.notation true
notation `i` c `t` t:45 `e` e:45 := ite c t e
#check i↥tt t 3 e 45
run_cmd do
  f1 ← tactic.to_expr ```(i↥tt t 3 e 45) >>= tactic.pp,
  f2 : format ← pure $ to_fmt "i↥tt t 3 e 45",
  tactic.trace f1,
  guard $ f1.to_string = f2.to_string

