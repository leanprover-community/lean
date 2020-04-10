universe u

inductive attr (α : Type) : Type
| val (name : string) (value : string) : attr
| on_click : (unit → α) → attr
-- | on_mouse : (mouse_event_args → α) → attr
| style : list (string × string) → attr

inductive html (α : Type) : Type
| element : string → list (attr α) → html → html
| of_string : string → html
| empty : html
| append : html→ html→ html

-- | stateful {α β σ : Type} : σ → (β → state σ α) → (σ → widget β) → widget α
-- | memoise
-- |

-- inductive json
-- | mk_array  : list json → json
-- | mk_object : list (string × json) → json
-- | mk_string : string → json
-- | mk_number : int → json
-- | mk_bool : bool → json

structure widget (α : Type) :=
(β : Type)
(σ : Type)
(init   : σ)
(update (state : σ) (action : β) : (σ × α))
(view   (state : σ) : html β)

/- keep everything as concrete as possible but stay open to wacky abstractions.
The component system needs:
- events with actions;
- statefulness
- timers / animation frames? [todo]
- how to interface with tactics? for now just treat it as global state and make `widget (tactic α)`.

How does it work?
When save_widget is called, the vm_obj for that widget is saved in the info manager.

I can index event handlers in 2 ways;
in way 1 I will use the vm index, but I do then need to keep the handler objects alive in the cache by keeping the reference count up.

Issues with thread safety are going to be a problem.-/

-- [todo] replace `widget unit` with `widget update` where update is some editor instruction to fill a hole.
meta constant tactic.save_widget : pos → (tactic_state → widget unit) → tactic unit

/- EXAMPLE: -/

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
meta def hello_world_widget (ts : tactic_state) : widget unit :=
widget.mk unit unit () (λ s b, (s,s)) (λ s, html.of_string "hello world")

meta def save_info (p : pos) : my_tactic unit := do
  tactic.save_info_thunk p (λ _, to_fmt "HELLO HERE IS SOME INFO"),
  -- tactic.save_widget p hello_world_widget,
  pure ()

end my_tactic

example {P Q : Prop} : P → Q → P :=
begin [my_tactic]
  tactic.intros,
  tactic.assumption
end

example {P Q : Prop} : P → Q → P :=
begin
  tactic.intros,
  tactic.assumption
end

#eval "adsf"