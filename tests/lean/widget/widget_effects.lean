
open widget
meta def effect_c : component tactic_state empty :=
widget.component.with_state unit nat (λ _, 0) (λ _ _ x, x) (λ _ x _, (x+1,none))
$ widget.component.with_effects (λ _ _, [
    effect.reveal_position none (pos.mk 60 14),
    effect.insert_text_relative 3 "hello",
    effect.custom "hello" "world",
    effect.highlight_position (some "hello/world.lean") ⟨3,4⟩,
    effect.clear_highlighting,
    effect.clear_highlighting,
    effect.clear_highlighting
  ])
$ widget.component.pure (λ ⟨s,p⟩, [to_string s, button "+" ()])

#html effect_c











































-- should reveal this!










