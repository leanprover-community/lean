import widget

meta def my_tactic := state_t unit tactic
namespace my_tactic
section
local attribute [reducible] my_tactic
meta instance : monad my_tactic := by apply_instance
meta instance : monad_state unit my_tactic := by apply_instance
meta instance : has_monad_lift tactic my_tactic := by apply_instance
end
meta instance (α : Type) : has_coe (tactic α) (my_tactic α) := ⟨monad_lift⟩
open interaction_monad.result
meta def step {α : Type} (m : my_tactic α) : my_tactic unit :=
m >> pure ()
/- istep is used to make an interactive thingy.  -/
meta def istep {α : Type} (line0 col0 line col : nat) (t : my_tactic α) : my_tactic unit :=
⟨λ v s,
  match (@scope_trace _ line col (λ _, t.run v s)) with
  | (success ⟨a,v⟩ s') := success ((),v) s'
  | (exception (some msg) p s') := exception (some msg) (some ⟨line, col⟩) s'
  | (exception none p s') := silent_fail s'
  end
⟩
meta instance : interactive.executor my_tactic :=
{ config_type := unit,
  execute_with := λ n tac, tac.run n >> pure ()
}
open html

meta def depth_test_component : component nat empty :=
component.stateless (λ n, match n with | 0 := ["0"] | (n+1) := [n, " ", html.of_component n depth_test_component] end)

meta def save_info (p : pos) : my_tactic unit := do
  -- tactic.save_info_thunk p (λ _, to_fmt "HELLO HERE IS SOME INFO"),
  tactic.save_widget p (widget.tactic_state_widget),
  -- tactic.save_widget p (component.stateless (λ t, [html.of_component 1000 depth_test_component])),
  -- tactic.save_widget p $ component.stateless (λ p, [of_component p counter_widget, of_component p counter_widget] ),
  pure ()

end my_tactic

example {P Q : Prop} : P → Q → P ∧ Q :=
begin [my_tactic]
  tactic.trace "a message",
  tactic.intros,
  tactic.split,
  tactic.assumption, tactic.assumption,
end

example {P Q : Prop} : P → Q → P :=
begin
  tactic.intros,
  tactic.assumption
end

#eval "adsf"