inductive foo (α β : Type)

def bar (β α) := foo α β

@[recursor 4]
lemma bar.induction_on {β α} {C : bar β α → Prop} (x : bar β α) : C x :=
by cases x

example {β α} (x : bar β α) : x = x :=
by induction x using bar.induction_on