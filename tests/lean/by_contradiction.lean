open tactic nat

example (a b : nat) : a ≠ b → ¬ a = b :=
by do
  intros,
  by_contradiction `H,
  trace_state,
  contradiction

#print "-------"

example (a b : nat) : ¬¬ a = b → a = b :=
by do
  intros,
  by_contradiction,
  trace_state,
  contradiction

#print "-------"

example (p q : Prop) : ¬¬ p → p :=
by do
  intros,
  by_contradiction `H,
  trace_state,
  contradiction
