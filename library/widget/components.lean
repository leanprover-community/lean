import widget.html

open html

/-- An example component which makes a 'like button'. One of the first examples from react. -/
meta def example_like_widget : component unit empty :=
-- trace "this is making a widget happen" $
component.mk unit bool (λ _ _, ff) (λ _ s b, (tt, none)) (λ _ s,
  if s then "you liked this!" else
  div [html.of_string "here is a comment ", button "like this" ()]
)

/-- A simple counter that can be incremented or decremented with some buttons. -/
meta def counter_widget {π α : Type} : component π α :=
component.mk int int (λ p x, 0 <| x) (λ _ x y, (x + y, none)) (λ _ s,
  div [
    button "+" (1 : int),
    of_string $ to_string $ s,
    button "-" (-1)
  ]
)

meta def with_hover {π α : Type} (tooltip : π → html α) (elt : π → element α) : component π α :=
component.mk (bool ⊕ α) bool
  (λ props prev, ff <| prev)
  (λ props state event,
    match event with
    | (sum.inl state') := (state', none)
    | (sum.inr a) := (state, some a)
    end)
  (λ props state,
    let elt : element (bool ⊕ α) := element.map_action sum.inr $ elt props in
    let atrs : list (attr (bool ⊕ α)) := [attr.on_mouse_enter (λ _, sum.inl tt), attr.on_mouse_leave (λ _, sum.inl ff)] in
    [
      if state then
        html.of_element $ element.with_attrs atrs elt
      else
        html.of_element $ element.with_attrs ((attr.tooltip $ map_action sum.inr $ tooltip props) :: atrs) elt
    ])