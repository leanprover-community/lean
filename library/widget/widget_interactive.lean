import .interactive_expr

/-- General purpose tactic for use with the widget system, setting the state to a component will render that component,
so you can use this to show arbitrary components.
The plan is that this will eventually replace `tactic`.
 -/
meta def widget_tactic := state_t (component tactic_state string) tactic

namespace widget_tactic
section
local attribute [reducible] widget_tactic
meta instance : monad widget_tactic := by apply_instance
meta instance : monad_state (component tactic_state string) widget_tactic := by apply_instance
meta instance : has_monad_lift tactic widget_tactic := by apply_instance
end
meta instance (α : Type) : has_coe (tactic α) (widget_tactic α) := ⟨monad_lift⟩
open interaction_monad.result
meta def step {α : Type} (m : widget_tactic α) : widget_tactic unit :=
m >> pure ()
/- istep is used to make an interactive thingy.  -/
meta def istep {α : Type} (line0 col0 line col : nat) (t : widget_tactic α) : widget_tactic unit :=
⟨λ v s,
  match (@scope_trace _ line col (λ _, t.run v s)) with
  | (success ⟨a,v⟩ s') := success ((),v) s'
  | (exception (some msg) p s') := exception (some msg) (some ⟨line, col⟩) s'
  | (exception none p s') := silent_fail s'
  end
⟩
meta instance : interactive.executor widget_tactic :=
{ config_type := unit,
  execute_with := λ n tac, tac.run (widget.tactic_state_widget) >> pure ()
}
open html

meta def depth_test_component : component nat empty :=
component.stateless (λ n, match n with | 0 := ["0"] | (n+1) := [n, " ", html.of_component n depth_test_component] end)

meta def save_info (p : pos) : widget_tactic unit := do
  comp ← get,
  tactic.save_widget p comp,
  pure ()

end widget_tactic