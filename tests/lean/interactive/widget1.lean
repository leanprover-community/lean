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
meta def like_widget (ts : tactic_state) : widget unit :=
-- trace "this is making a widget happen" $
widget.mk unit bool ff (λ s b, (tt,b)) (λ s,
  if s then "you liked this!" else
  div ["here is a comment ", button "like this" ()]
)

meta def counter_widget (ts : tactic_state) : widget unit :=
widget.mk int int 0 (λ x y, (x + y, ())) (λ s,
  div [
    button "+" 1,
    to_string s,
    button "-" (-1)
  ]
)

meta def with_pos_widget (p : pos) (w : widget unit) : widget unit :=
{ view := λ s, div [div [to_string p.line, ":", to_string p.column], w.view s], ..w}

meta def save_info (p : pos) : my_tactic unit := do
  tactic.save_info_thunk p (λ _, to_fmt "HELLO HERE IS SOME INFO"),
  tactic.save_widget p (λ ts, with_pos_widget p $ counter_widget ts),
  pure ()

end my_tactic

example {P Q : Prop} : P → Q → P ∧ Q :=
begin [my_tactic]
  tactic.trace "a message",
                    --^ "command": "info"
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