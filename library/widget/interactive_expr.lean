/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
import widget.basic widget.tactic_component

meta def subexpr := (expr × expr.address)

namespace widget

open tagged_format
open html attr

def format.color.to_string : format.color → string
| format.color.red := "red" | format.color.green := "green" | format.color.orange := "orange" | format.color.blue := "blue" | format.color.pink := "pink" | format.color.cyan := "cyan" | format.color.grey := "grey"


namespace interactive_expression

/-- eformat but without any of the formatting stuff like highlighting, groups etc. -/
meta inductive sf : Type
| tag_expr : expr.address → expr → sf → sf
| compose : sf →  sf →  sf
| of_string : string →  sf

private meta def to_simple : eformat → sf
| (tag ⟨ea,e⟩ m) := sf.tag_expr ea e $ to_simple m
| (group m) := to_simple m
| (nest i m) := to_simple m
| (highlight i m) := to_simple m
| (of_format f) := sf.of_string $ format.to_string f
| (compose x y) := sf.compose (to_simple x) (to_simple y)

private meta def sf.flatten : sf → sf
| (sf.tag_expr e ea m) := (sf.tag_expr e ea $ sf.flatten m)
| (sf.compose x y) :=
  match (sf.flatten x), (sf.flatten y) with
  | (sf.of_string sx), (sf.of_string sy) := sf.of_string (sx ++ sy)
  | (sf.of_string sx), (sf.compose (sf.of_string sy) z) := sf.compose (sf.of_string (sx ++ sy)) z
  | (sf.compose x (sf.of_string sy)), (sf.of_string sz) := sf.compose x (sf.of_string (sy ++ sz))
  | (sf.compose x (sf.of_string sy1)), (sf.compose (sf.of_string sy2) z) := sf.compose x (sf.compose (sf.of_string (sy1 ++ sy2)) z)
  | x, y := sf.compose x y
  end
| (sf.of_string s) := sf.of_string s

meta inductive action (γ : Type)
| on_mouse_enter : subexpr → action
| on_mouse_leave_all : action
| on_click : subexpr → action
| on_tooltip_action : γ → action
| on_close_tooltip : action

meta def view {γ} (tooltip_component : tc subexpr (action γ)) (click_address : option expr.address) (select_address : option expr.address) :
  subexpr → sf → tactic (list (html (action γ)))
| ⟨ce, current_address⟩ (sf.tag_expr ea e m) := do
  let new_address := current_address ++ ea,
  let select_attrs : list (attr (action γ)) := if some new_address = select_address then [className "highlight"] else [],
  click_attrs  : list (attr (action γ)) ←
    if some new_address = click_address then do
      content ← tc.to_html tooltip_component (e, new_address),
      pure [tooltip $ content]
    else pure [],
  let as := [className "expr-boundary", key (ea)] ++ select_attrs ++ click_attrs,
  inner ← view (e,new_address) m,
  pure [h "span" as inner]
| ca (sf.compose x y) := pure (++) <*> view ca x <*> view ca y
| ca (sf.of_string s) := pure
  [h "span" [
    on_mouse_enter (λ _, action.on_mouse_enter ca),
    on_click (λ _, action.on_click ca),
    key s
  ] [html.of_string s]]


/-- Make an interactive expression. -/
meta def mk {γ} (tooltip : tc subexpr γ) : tc expr γ :=
let tooltip_comp :=
   component.with_props_eq (λ (x y : tactic_state × expr × expr.address), x.2.2 = y.2.2)
   $ component.map_action (action.on_tooltip_action) tooltip in
tc.mk_simple
  (action γ)
  (option subexpr × option subexpr)
  (λ e, pure $ (none, none))
  (λ e ⟨ca, sa⟩ act, pure $
    match act with
    | (action.on_mouse_enter ⟨e, ea⟩) := ((ca, some (e, ea)), none)
    | (action.on_mouse_leave_all)     := ((ca, none), none)
    | (action.on_click ⟨e, ea⟩)       := if some (e,ea) = ca then ((none, sa), none) else ((some (e, ea), sa), none)
    | (action.on_tooltip_action g)    := ((none, sa), some g)
    | (action.on_close_tooltip)       := ((none, sa), none)
    end
  )
  (λ e ⟨ca, sa⟩, do
    ts ← tactic.read,
    let m : sf  := sf.flatten $ to_simple $ tactic_state.pp_tagged ts e,
    let m : sf  := sf.tag_expr [] e m, -- [hack] in pp.cpp I forgot to add an expr-boundary for the root expression.
    v ← view tooltip_comp (prod.snd <$> ca) (prod.snd <$> sa) ⟨e, []⟩ m,
    pure $
    [ h "span" [
          className "expr",
          key e.hash,
          on_mouse_leave (λ _, action.on_mouse_leave_all) ] $ v
      -- expr.address.to_string $ match ca with | none := [] | (some ⟨x,y⟩) := y end,
      -- expr.address.to_string $ match sa with | none := [] | (some ⟨x,y⟩) := y end
      ]
  )

/-- Render the implicit arguments for an expression in fancy, little pills. -/
meta def implicit_arg_list (tooltip : tc subexpr empty) (e : expr) : tactic $ html empty := do
  fn ← (mk tooltip) $ expr.get_app_fn e,
  args ← list.mmap (mk tooltip) $ expr.get_app_args e,
  pure $ h "div" []
    ( (h "span" [className "bg-blue br3 ma1 ph2 white"] [fn]) ::
      list.map (λ a, h "span" [className "bg-gray br3 ma1 ph2 white"] [a]) args
    )

meta def type_tooltip : tc subexpr empty :=
tc.stateless (λ ⟨e,ea⟩, do
    y ← tactic.infer_type e,
    y_comp ← mk type_tooltip y,
    implicit_args ← implicit_arg_list type_tooltip e,
    pure [
        h "div" [] [
          h "div" [] [y_comp],
          h "hr" [] [],
          implicit_args,
          h "hr" [] [],
          h "div" [className "gray"] [
            ea.to_string
          ]
        ]
      ]
  )

end interactive_expression

meta def html.of_name {α : Type} : name → html α
| n := html.of_string $ name.to_string n

open tactic

meta def show_type_component : tc expr empty :=
tc.stateless (λ x, do
  y ← infer_type x,
  y_comp ← interactive_expression.mk interactive_expression.type_tooltip $ y,
  pure y_comp
)

meta def tactic_view_component {γ} (local_c : tc expr γ) (target_c : tc expr γ) : tactic (html γ) :=
do
  gs ← get_goals,
  hs : list (html γ) ← gs.mmap (λ g, do
    ts ← read,
    gn ← pp g,
    set_goals [g],
    lcs ← local_context,
    lchs : list (html γ) ← lcs.mmap (λ lc, do
      pn ← pure $ expr.local_pp_name lc,
      lh : html γ ← local_c lc,
      pure
        $ h "tr" [key $ to_string $ expr.local_uniq_name lc] [
            h "td" [] [html.of_name pn],
            h "td" [] [html.of_string " : "],
            h "td" [] [lh]
        ]
    ),
    t_comp ← target_c g,
    (expr.mvar u_n pp_n y) ← pure g,
    pure $ h "table" [key $ expr.hash g, className "font-code"] [
      h "tbody" [] $ lchs ++ [
          h "tr" [key u_n, className "bt"] [
            h "td" [] [] ,
            h "td" [] [html.of_string " ⊢ "],
            h "td" [] [t_comp]
       ]]
    ]
  ),
  set_goals gs,
  pure $ h "ul" [className "list pl0"]
       $ list.map_with_index (λ i x,
         let border_cn := if i + 1 = hs.length then "ba bl-0 bt-0 br-0 b--dotted b--black-30" else "" in
         h "li" [className $ "lh-copy " ++ border_cn] [x])
       $ hs


meta def tactic_render : tactic (html empty) :=
tactic_view_component show_type_component show_type_component

meta def mk_tactic_widget {α β σ : Type}
  (init : σ)
  (update : σ → β → tactic (σ × α))
  (view : σ → tactic (html β))
  (error : option format → σ → σ) : component tactic_state α :=
component.mk β (σ × tactic_state)
  (λ ts_new prev, match prev with | (some ⟨s,ts_old⟩) := ⟨s, ts_new⟩ | (none) := ⟨init, ts_new⟩ end)
  (λ _ ⟨s,ts⟩ b,
      match update s b ts with
      | (interaction_monad.result.success ⟨s,a⟩ ts) := ⟨⟨s,ts⟩, some a⟩
      | (interaction_monad.result.exception msg pos _) := ⟨⟨s,ts⟩, none⟩
      end
  )
  (λ _ ⟨s,ts⟩,
      match view s ts with
      | (interaction_monad.result.success x ts) := x
      | (interaction_monad.result.exception msg pos ts) := [html.of_string "view errored"]
      end
  )
  (λ x y, ff)

meta def tactic_state_widget : component tactic_state string :=
mk_tactic_widget () (λ _ _, failure) (λ _, tactic_render) (λ _ x, x)

end widget



