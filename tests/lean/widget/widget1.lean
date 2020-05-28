
open widget

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

meta def string_todo_list : component tactic_state string :=
component.map_action (λ (o : empty), empty.rec (λ _, _) o) $ component.map_props (λ p, ()) $
todo_list string ["make some tasks", "delete some tasks"]

#html string_todo_list
