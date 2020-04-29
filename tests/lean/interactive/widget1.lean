import widget

example {P Q : Prop} : P → Q → P ∧ Q :=
begin [widget_tactic]
  tactic.intros,
  tactic.split,
  tactic.assumption, tactic.assumption,
end
