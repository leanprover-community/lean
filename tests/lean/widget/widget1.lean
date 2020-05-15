import widget

example {P Q : Prop} : P → Q → P ∧ Q :=
begin [widget_tactic]
  put (widget.examples.string_todo_list),
  tactic.intros,
  tactic.split,
  tactic.assumption, tactic.assumption,
end
