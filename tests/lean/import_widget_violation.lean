

/- The issue this is checking is whether vm_overrides are preserved in oleans.
It will segfault if not. -/

#check tactic.save_info_with_widgets

run_cmd tactic.save_info_with_widgets ⟨1,2⟩ *> tactic.trace "hello"
run_cmd tactic.save_info ⟨1,2⟩ *> tactic.trace "hello"

-- sometimes segfaults because inliner using a bad vm_decls
example {P : Type} : P → P :=
begin
  intros, assumption
end

inductive hello
| a : hello → hello
| b : hello