
open widget

meta class has_show_html (π : Type) :=
(show_html' {α : Type}: π → html α)

meta def show_html {π α : Type} [has_show_html π] : π → html α := has_show_html.show_html'

meta instance string_show_html : has_show_html string := ⟨λ α p, html.of_string p⟩

meta class has_to_editor (π : Type) :=
(comp : π → html π)

meta def to_editor (π : Type) [inhabited π] [has_to_editor π] : component unit π :=
component.with_state π π
  (λ _, default)
  (λ _ _, id)
  (λ _ po pn, (pn, some pn))
  $ component.pure (λ ⟨c,_⟩, [has_to_editor.comp c])

meta instance string_editor : has_to_editor string :=
⟨λ s, textbox s (λ s', s')⟩

inductive todo_list_action (α : Type)
| insert : α → todo_list_action
| delete : nat → todo_list_action

meta def todo_list (α : Type) [inhabited α] [decidable_eq α] [has_show_html α] [has_to_editor α] (initial : list α) : component unit empty :=
  let starts : list (ℕ × α) := initial.map_with_index prod.mk in
  component.stateful (todo_list_action α) (nat × list (nat × α))
  (λ _ last, ⟨starts.length, starts⟩ <| last)
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
                  $ component.stateful (option α) α
                      (λ p last, default <| last)
                      (λ ⟨⟩ x b, match b with none := (default, some x) | (some x') := (x', none) end)
                      (λ ⟨⟩ x,  [ h "div" [className "dtc v-mid"]
                                    [html.map_action some $ has_to_editor.comp x]
                                , h "button"
                                    [className "dtc v-mid f6 button-reset bg-white ba b--black-20 dim pointer pv1 w2"
                                    , on_click (λ _, none)]
                                    ["+"]
                                ])]]])

meta def string_todo_list : component tactic_state empty :=
component.map_action (λ (o : empty), empty.rec (λ _, _) o) $ component.map_props (λ p, ()) $
todo_list string ["make some tasks", "delete some tasks"]

#html string_todo_list
