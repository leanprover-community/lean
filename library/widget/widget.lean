import .html

universe u

meta def widget.mk_tactic_widget {α β σ : Type}
  (init : σ)
  (update : σ → β → tactic (σ × α))
  (view : σ → tactic (html β))
  (error : option format → σ → σ) : component tactic_state α :=
component.mk β (σ × tactic_state)
  (λ ts_new prev, match prev with | (some ⟨s,ts_old⟩) := ⟨s, ts_new⟩ | (none) := ⟨init, ts_new⟩ end)
  (λ _ ⟨s,ts⟩ b,
      match update s b ts with
      | (interaction_monad.result.success ⟨s,a⟩ ts) := ⟨⟨s,ts⟩, some a⟩
      | (interaction_monad.result.exception msg pos _) := ⟨⟨s,ts⟩, none⟩
      end
  )
  (λ _ ⟨s,ts⟩,
      match view s ts with
      | (interaction_monad.result.success x ts) := x
      | (interaction_monad.result.exception msg pos ts) := [html.of_string "view errored"]
      end
  )