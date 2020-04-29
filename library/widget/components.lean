import widget.html

open html

namespace component


meta class has_show_html (π : Type) :=
(show_html' {α : Type}: π → html α)

meta def show_html {π α : Type} [has_show_html π] : π → html α := has_show_html.show_html'

meta instance string_show_html : has_show_html string := ⟨λ α p, html.of_string p⟩

meta class has_to_editor (π : Type) :=
(comp : π → html π)

meta def to_editor (π : Type) [inhabited π] [has_to_editor π] : component unit π :=
component.mk π π
(λ ⟨⟩ x, inhabited.default _ <| x)
(λ ⟨⟩ x x', (x', some x'))
(λ ⟨⟩ x, has_to_editor.comp x)

meta instance string_editor : has_to_editor string :=
⟨λ s, html.textbox s (λ s', s')⟩

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
        html.of_element $ element.with_attrs ((attr.tooltip $ html.map_action sum.inr $ tooltip props) :: atrs) elt
    ])

meta instance ignore_action {π α : Type} : has_coe (component π α) (component π empty) :=
⟨component.filter_map_action (λ a, none)⟩

meta instance component_of_no_action {π α : Type}: has_coe (component unit empty) (component π α) :=
⟨λ c, component.map_action (λ o, empty.rec (λ _, α) o) $ component.map_props (λ p, ()) $ c⟩

inductive todo_list_action (α : Type)
| insert : α → todo_list_action
| delete : nat → todo_list_action
-- todo: move

meta def todo_list (α : Type) [inhabited α] [has_show_html α] [has_to_editor α] : component unit empty :=
component.mk (todo_list_action α) (nat × list (nat × α))
(λ _ x, ⟨0, []⟩ <| x )
(λ ⟨⟩ ⟨i,items⟩ b,
  match b with
  | (todo_list_action.insert a) := ((i+1, (i,a) :: items), none)
  | (todo_list_action.delete j) := ((i, items.filter (λ p, p.1 = j)), none)
  end
)
(λ ⟨⟩ ⟨i,items⟩,
  [ html.h "ol" [] $ items.map (λ ⟨k,a⟩,
      html.h "li" [attr.key k] [show_html a, html.button "X" (todo_list_action.delete k)]
      ),
    html.map_action (λ x, todo_list_action.insert x)
    $ html.of_component ()
    $ @component.mk α unit (option α) α
      (λ ⟨⟩ prev, inhabited.default α <| prev)
      (λ ⟨⟩ x b, match b with none := (inhabited.default α, some x) | (some x') := (x', none) end)
      (λ ⟨⟩ x, [html.map_action some $ has_to_editor.comp x, html.button "+" (none)])
  ]
)


end component