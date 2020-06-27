open widget

meta def effect_c : component tactic_state widget.effects :=
widget.component.mk
  unit
  nat
  (λ p s,(0) <| s)
  (λ p ls ⟨⟩, ⟨ls + 1, some ([
    effect.reveal_position none (pos.mk 60 14),
    effect.insert_text "hello",
    effect.custom "hello" "world",
    effect.highlight_position (some "hello/world.lean") ⟨3,4⟩,
    effect.clear_highlighting,
    effect.clear_highlighting,
    effect.clear_highlighting
  ])⟩)
  (λ p s, [to_string s, button "+" (), " *** "]) (λ a b, ff)

#html effect_c















































-- reveals __here!__


