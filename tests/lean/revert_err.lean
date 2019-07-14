open tactic

example (a b : Prop) : true :=
by do to_expr ```(a ∧ b) >>= revert

example {α : Type} {a : α} : true :=
by revert a a
