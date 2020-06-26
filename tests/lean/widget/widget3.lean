
open widget

meta def asdf_c (message : list string) : component nat empty :=
widget.component.mk
  unit
  (list nat)
  (λ p s, p :: ([] <| s))
  (λ p ls x, (ls,none))
  (λ p ss, [h "div" [] [html.of_string $ to_string p ++ to_string message ++ to_string ss], button "asdf" ()]) (λ a b, a = b)

meta def qwerty_c : component tactic_state widget.effects :=
widget.component.mk
  unit
  nat
  (λ p s,(0) <| s)
  (λ p ls ⟨⟩, ⟨ls + 1, none⟩)
  (λ p s, [to_string s, button "+" (), html.of_component s (asdf_c [" *** "])]) (λ a b, ff)

#html qwerty_c

-- the point of this test is to see whether the state is kept even if the child component is rerendered.
-- so after hitting '+', you should see `1[ *** ][1, 0]` which means that 'init' was called again with the carried over state.
-- hitting asdf should not do anything.