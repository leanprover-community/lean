open widget
variables {π α : Type}

-- set_option trace.compiler true

meta def f : mouse_capture_state → string
| mouse_capture_state.child := "ba b--blue"
| mouse_capture_state.outside := "ba b--red"
| mouse_capture_state.immediate := "ba b--green"

#eval f $ unchecked_cast tt

meta def mouse_comp : (list (html nat)) → (html nat)
| v := html.of_component ()
$ component.with_mouse
$ component.map_props (λ ⟨m, ⟨⟩⟩, m)
$ component.pure (λ m,
[h "div" [cn $ "ma3 pa3 " ++ f m, on_mouse_enter (λ _, 1)] $
[to_string $ @unchecked_cast _ nat $ m] ++ v])

meta def blank_comp : html α → html α
| x := html.of_component ()
$ component.pure (λ ⟨⟩, [h "div" [cn "ma3 pa3 b--silver ba"] [x]])

meta def test_comp : html α :=
html.of_component ()
$ component.with_state _ _ (λ _, 0) (λ _ _ x, x) (λ _ s x, (s + x, none))
$ component.pure $ λ ⟨n,_⟩, h "div" [] [
  mouse_comp ["hello"],
  mouse_comp [
    mouse_comp [
      mouse_comp ["asdf"],
      mouse_comp ["qwerty"]
    ],
    blank_comp $ mouse_comp ["foo", blank_comp ["world"]]
  ],
  to_string n
]

#html test_comp