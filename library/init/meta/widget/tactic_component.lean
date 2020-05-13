import init.meta.tactic
import init.meta.widget.basic

meta def tactic.run_simple {α} : tactic_state → tactic α → option α
| ts t := match t ts with
          | (interaction_monad.result.success a ts') := some a
          | (interaction_monad.result.exception _ _ _) := none
          end

namespace widget

/-- A component that implicitly depends on tactic_state. For efficiency we always assume that the tactic_state is unchanged between component renderings. -/
meta def tc (π : Type) (α : Type) := component (tactic_state × π) (α)

namespace tc

variables {π ρ α β : Type}

meta def of_component : component π α → tc π α :=
component.map_props prod.snd

meta def map_action (f : α → β) : tc π α → tc π β :=
component.map_action f

meta def map_props (f : π → ρ) : tc ρ α → tc π α :=
component.map_props (prod.map id f)


open interaction_monad
open interaction_monad.result

/-- Make a tactic component from some init, update, views which are expecting a tactic.
Note that the resulting tactic state of the view is thrown away but tactic_state is preserved locally on updates.

-/
meta def mk_simple
  [decidable_eq π]
  (β σ : Type)
  (init : π → tactic σ)
  (update : π → σ → β → tactic (σ × option α))
  (view : π → σ → tactic (list (html β)))
  : tc π α :=
@component.mk
  (tactic_state × π)
  α
  β
  (interaction_monad.result tactic_state σ)
  (λ ⟨ts,p⟩ last, match last with (some x) := x | _ := init p ts end)
  (λ ⟨ts,p⟩ s b,
    match s with
    | (success s ts) :=
      match update p s b ts with
      | (success ⟨s,a⟩ ts) := prod.mk (success s ts) (a)
      | (exception m p s) := prod.mk (exception m p s) none
      end
    | x := ⟨x,none⟩
    end
  )
  (λ ⟨ts,p⟩ s,
    match s with
    | (success s ts) :=
      match view p s ts with
      | (success h ts) := h
      | (exception msg pos s) := ["rendering tactic failed "]
      end
    | (exception msg pos s) := ["state of tactic component has failed!"]
    end
  )
  (λ ⟨_,p1⟩ ⟨_,p2⟩, p1 = p2)

-- meta def run : tc unit α → component tactic_state α
-- | c := component.mk _ _ (λ )

end tc

end widget