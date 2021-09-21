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
  by_contradiction `H,
  trace_state,
  contradiction

#print "-------"

example (p q : Prop) : ¬¬ p → p :=
by do
  intros,
  by_contradiction `H,
  trace_state,
  contradiction

-- following tests use interactive mode so that we can use `guard_hyp`


/-- `by_contradiction` should unfold reducible defs like `ne` to find a leading `not`. --/
example (a b : nat) : a ≠ b → a ≠ b :=
begin
  intros,
  by_contradiction H,
  guard_hyp H : a = b,
  contradiction
end

def my_ne (a b : nat) := a ≠ b

/-- Semireducible defs are not unfolded -/
example (a b : nat) : a ≠ b → my_ne a b :=
begin
  intros,
  by_contradiction H,
  guard_hyp H : ¬my_ne a b,
  contradiction
end
