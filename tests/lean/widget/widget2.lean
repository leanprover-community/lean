
open widget

/-- A simple counter that can be incremented or decremented with some buttons. -/
meta def counter_widget {π α : Type} : component π α :=
component.ignore_props $ component.stateful int int (λ _ x, 0 <| x) (λ _ x y, (x + y, none)) (λ _ s,
  h "div" [] [
    button "+" (1 : int),
    html.of_string $ to_string $ s,
    button "-" (-1)
  ]
)

#html counter_widget
