open widget

meta def effect_c : component tactic_state widget.effects :=
widget.component.mk
  unit
  nat
  (λ p s,(0) <| s)
  (λ p ls ⟨⟩, ⟨ls + 1, some ([
    effect.reveal_position none (pos.mk 60 14)
  ])⟩)
  (λ p s, [to_string s, button "+" (), " *** "]) (λ a b, ff)

#html effect_c















































-- reveals __here!__


