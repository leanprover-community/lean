/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import init.meta.widget.basic

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
The tactic_state never mutates.
-/
meta def mk_simple
  [decidable_eq π]
  (β σ : Type)
  (init : π → tactic σ)
  (update : π → σ → β → tactic (σ × option α))
  (view : π → σ → tactic (list (html β)))
  : tc π α :=
component.with_should_update (λ ⟨_,old_p⟩ ⟨_,new_p⟩, old_p ≠ new_p)
$ @component.stateful
  (tactic_state × π)
  α
  β
  (interaction_monad.result tactic_state σ)
  (λ ⟨ts,p⟩ last,
    match last with
    | (some x) := x
    | none := init p ts
    end)
  (λ ⟨ts,p⟩ s b,
    match s with
    | (success s _) :=
      match update p s b ts with
      | (success ⟨s,a⟩ _) := prod.mk (success s ts) (a)
      | (exception m p ts') := prod.mk (exception m p ts') none
      end
    | x := ⟨x,none⟩
    end
  )
  (λ ⟨ts,p⟩ s,
    match s with
    | (success s _) :=
      match view p s ts with
      | (success h _) := h
      | (exception msg pos s) := ["rendering tactic failed "]
      end
    | (exception msg pos s) := ["state of tactic component has failed!"]
    end
  )

meta def stateless [decidable_eq π] (view : π → tactic (list (html α))) : tc π α :=
tc.mk_simple α unit (λ p, pure ()) (λ _ _ b, pure ((),some b)) (λ p _, view p)

meta def to_html : tc π α → π → tactic (html α)
| c p ts := success (html.of_component (ts,p) c) ts

meta def to_component : tc unit α → component tactic_state α
| c := component.map_props (λ tc, (tc,())) c

meta instance : has_coe_to_fun (tc π α) (λ x, π → tactic (html α)) := ⟨to_html⟩

end tc

end widget
