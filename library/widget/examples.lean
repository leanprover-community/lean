/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
namespace widget

meta class has_show_html (π : Type) :=
(show_html' {α : Type}: π → html α)

meta def show_html {π α : Type} [has_show_html π] : π → html α := has_show_html.show_html'

meta instance string_show_html : has_show_html string := ⟨λ α p, html.of_string p⟩

meta class has_to_editor (π : Type) :=
(comp : π → html π)

meta def to_editor (π : Type) [inhabited π] [has_to_editor π] : component unit π :=
component.mk_simple π π
(inhabited.default π)
(λ ⟨⟩ x x', (x', some x'))
(λ ⟨⟩ x, has_to_editor.comp x)

meta instance string_editor : has_to_editor string :=
⟨λ s, textbox s (λ s', s')⟩

namespace examples

/-- An example component which makes a 'like button'. One of the first examples from react. -/
meta def example_like_widget : component unit empty :=
-- trace "this is making a widget happen" $
component.mk_simple unit bool (ff) (λ _ s b, (tt, none)) (λ _ s,
  if s then "you liked this!" else
  h "div" [] [html.of_string "here is a comment ", button "like this" ()]
)

/-- A simple counter that can be incremented or decremented with some buttons. -/
meta def counter_widget {π α : Type} : component π α :=
component.ignore_props $ component.mk_simple int int 0 (λ _ x y, (x + y, none)) (λ _ s,
  h "div" [] [
    button "+" (1 : int),
    html.of_string $ to_string $ s,
    button "-" (-1)
  ]
)

meta def with_hover {π α : Type} [decidable_eq π] (tooltip : π → html α) (elt : π → html α) : component π α :=
component.mk_simple (bool ⊕ α) bool
  (ff)
  (λ props state event,
    match event with
    | (sum.inl state') := (state', none)
    | (sum.inr a) := (state, some a)
    end)
  (λ props state,
    let elt : html (bool ⊕ α) := html.map_action sum.inr $ elt props in
    let atrs : list (attr (bool ⊕ α)) := [on_mouse_enter (λ _, sum.inl tt), on_mouse_leave (λ _, sum.inl ff)] in
    [
      if state then
        with_attrs atrs elt
      else
        with_attrs ((attr.tooltip $ html.map_action sum.inr $ tooltip props) :: atrs) elt
    ])

meta def dotted_border_list {α β : Type} (get_key : β → string) (view : β → html α ) : list β → html α | l :=
h "div" [className "pa3 pa5-ns"] [
  h "ol" [className "list pl0 measure center"] $
  l.map (λ x,
    h "li" [className "lh-copy pv3 ba bl-0 bt-0 br-0 b--dotted b--black-30", key $ get_key x] $ view x
  )
]

inductive todo_list_action (α : Type)
| insert : α → todo_list_action
| delete : nat → todo_list_action

meta def todo_list (α : Type) [inhabited α] [decidable_eq α] [has_show_html α] [has_to_editor α] (initial : list α) : component unit empty :=
  let starts : list (ℕ × α) := initial.map_with_index prod.mk in
  component.mk_simple (todo_list_action α) (nat × list (nat × α))
  ⟨starts.length, starts⟩
  (λ ⟨⟩ ⟨i,items⟩ b,
    match b with
    | (todo_list_action.insert a) := ((i+1, items ++ [(i,a)]), none)
    | (todo_list_action.delete j) := ((i, items.filter (λ p, p.1 ≠ j)), none)
    end
  )
  (λ ⟨⟩ ⟨i,items⟩,
    [ h "div" [className "mw6"] $
      items.map (λ ⟨k,a⟩,
        h "div" [className "flex justify-between items-center w-100 bb b--black-20 pb2 mt2", key k] [
          h "div" [className "dtc v-mid"] [show_html a],
          h "button" [
            className "dtc v-mid f6 button-reset bg-white ba b--black-20 dim pointer pv1 w2",
            on_click (λ _, todo_list_action.delete $ k)] ["x"]
        ]
      ) ++  [ h "hr" [] []
            , h "div" [className "flex justify-between items-center w-100 bb b--black-20 pb2 mt2", key "add row"]
                [ html.map_action (λ x, todo_list_action.insert x)
                  $ html.of_component ()
                  $ component.mk_simple (option α) α
                      (inhabited.default α)
                      (λ ⟨⟩ x b, match b with none := (inhabited.default α, some x) | (some x') := (x', none) end)
                      (λ ⟨⟩ x,  [ h "div" [className "dtc v-mid"]
                                    [html.map_action some $ has_to_editor.comp x]
                                , h "button"
                                    [className "dtc v-mid f6 button-reset bg-white ba b--black-20 dim pointer pv1 w2"
                                    , on_click (λ _, none)]
                                    ["+"]
                                ])]]])

meta def simple_tooltip_component : component tactic_state empty :=
component.ignore_props $ component.stateless (λ _, [
  h "div" [
    className "grow dib bg-pink black-90 pa5",
    attr.tooltip (
      h "div" [className "pa3 bg-light-blue"] ["this is the tooltip content"]
    )] ["this is some text with a tooltip"]
])

meta def string_todo_list : component tactic_state string :=
component.map_action (λ (o : empty), empty.rec (λ _, _) o) $ component.map_props (λ p, ()) $
todo_list string ["make some tasks", "delete some tasks"]

/-- Performs a simple editor action for testing insertion to sourcetext. -/
meta def simple_action (cmd : string) : component tactic_state string :=
component.mk unit nat
(λ _ _, 0)
(λ _ n _, (n+1, some (cmd ++ to_string n)))
(λ _ n, [button ("add " ++ cmd ++ to_string n) ()])
(λ _ _, ff)

end examples

end widget