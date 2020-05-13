/- Author: E.W.Ayers -/
/- This contains an experimental attempt to get pretty printing to keep expression information so that the user can hover over subterms of an expression in a widget and get information about that subterm.
For example  -/
prelude
import init.meta.widget.basic
import init.meta.tactic
import init.meta.expr_address

/-- An alternative to format that keeps structural information about the expression.
For lack of a better name I called it `magic`, rename suggestions welcome.

On tag_expr, note that the given `expr` is _not_ necessarily the subexpression of the root expression that `tactic_state.pp_magic` was
called with. For example if the subexpression is under a binder then all of the `expr.var 0`s will be replaced with
a local not in the local context with the name and type set to that of the binder.
-/
meta inductive magic
| tag_expr : expr.address → expr → magic → magic
| compose : magic → magic → magic
| group : magic → magic
| nest : nat → magic → magic
| highlight : format.color → magic → magic
| format : format → magic

open format
meta def magic.to_fmt : magic → format
| (magic.compose m1 m2) := format.compose (magic.to_fmt m1) (magic.to_fmt m2)
| (magic.group m1) := format.group (magic.to_fmt m1)
| (magic.nest i m) := format.nest i $ magic.to_fmt m
| (magic.highlight c m) := format.highlight (magic.to_fmt m) c
| (magic.format f) := f
| (magic.tag_expr ea e m) := magic.to_fmt m

meta instance magic.has_to_fmt : has_to_format magic := ⟨magic.to_fmt⟩

/-- A special version of pp which also preserves expression boundary information. -/
meta constant tactic_state.pp_magic   : tactic_state → expr → magic

meta def tactic.pp_magic : expr → tactic magic
| e := tactic.read >>= λ ts, pure $ tactic_state.pp_magic ts e

meta def tactic.run_simple {α} : tactic_state → tactic α → option α
| ts t := match t ts with
          | (interaction_monad.result.success a ts') := some a
          | (interaction_monad.result.exception _ _ _) := none
          end

namespace widget

open magic
open html attr

def format.color.to_string : format.color → string
| format.color.red := "red" | format.color.green := "green" | format.color.orange := "orange" | format.color.blue := "blue" | format.color.pink := "pink" | format.color.cyan := "cyan" | format.color.grey := "grey"

/-- magic but without any of the formatting stuff like highlighting, groups etc. -/
meta inductive sm : Type
| tag_expr : expr.address → expr → sm → sm
| compose : sm →  sm →  sm
| of_string : string →  sm

meta def to_simple : magic → sm
| (magic.tag_expr ea e m) := sm.tag_expr ea e $ to_simple m
| (magic.group m) := to_simple m
| (magic.nest i m) := to_simple m
| (magic.highlight i m) := to_simple m
| (magic.format f) := sm.of_string $ format.to_string f
| (magic.compose x y) := sm.compose (to_simple x) (to_simple y)

meta def sm.flatten : sm → sm
| (sm.tag_expr e ea m) := (sm.tag_expr e ea $ sm.flatten m)
| (sm.compose x y) :=
  match (sm.flatten x), (sm.flatten y) with
  | (sm.of_string sx), (sm.of_string sy) := sm.of_string (sx ++ sy)
  | (sm.of_string sx), (sm.compose (sm.of_string sy) z) := sm.compose (sm.of_string (sx ++ sy)) z
  | (sm.compose x (sm.of_string sy)), (sm.of_string sz) := sm.compose x (sm.of_string (sy ++ sz))
  | (sm.compose x (sm.of_string sy1)), (sm.compose (sm.of_string sy2) z) := sm.compose x (sm.compose (sm.of_string (sy1 ++ sy2)) z)
  | x, y := sm.compose x y
  end
| (sm.of_string s) := sm.of_string s

namespace interactive_expression

meta inductive action (γ : Type)
| on_mouse_enter : (expr × expr.address) → action
| on_mouse_leave_all : action
| on_click : (expr × expr.address) → action
| on_tooltip_action : γ → action
| on_close_tooltip : action

meta def view {γ} (tooltip_component : component (expr × expr.address) (action γ)) (click_address : option expr.address) (select_address : option expr.address) :
  (expr × expr.address) → sm → list (html (action γ))
| ⟨ce, current_address⟩ (sm.tag_expr ea e m) :=
  let new_address := current_address ++ ea in
  let select_attrs : list (attr (action γ)) := if some new_address = select_address then [className "highlight"] else [] in
  let click_attrs  : list (attr (action γ)) := if some new_address = click_address  then [tooltip $ html.of_component (e, new_address) $ tooltip_component] else [] in
  let as := [className "expr-boundary", key (expr.hash e)] ++ select_attrs ++ click_attrs in
  [h "span" as $ view (e, new_address) m]
| ca (sm.compose x y) := view ca x ++ view ca y
| ca (sm.of_string s) :=
  [h "span" [
    on_mouse_enter (λ _, action.on_mouse_enter ca),
    on_click (λ _, action.on_click ca)
  ] [html.of_string s]]


/-- Make an interactive expression. -/
meta def mk {γ} (ts : tactic_state) (tooltip : component (expr × expr.address) γ) : component expr γ :=
let tooltip_comp := component.map_action (action.on_tooltip_action) tooltip in
component.mk
  (action γ)
  (option (expr × expr.address) × option (expr × expr.address))
  (λ e prev, (none, none))
  (λ e ⟨ca, sa⟩ act,
    match act with
    | (action.on_mouse_enter ⟨e, ea⟩) := ((ca, some (e, ea)), none)
    | (action.on_mouse_leave_all)     := ((ca, none), none)
    | (action.on_click ⟨e, ea⟩)       := if some (e,ea) = ca then ((none, sa), none) else ((some (e, ea), sa), none)
    | (action.on_tooltip_action g)    := ((none, sa), some g)
    | (action.on_close_tooltip)       := ((none, sa), none)
    end
  )
  (λ e ⟨ca, sa⟩,
    let m : sm  := sm.flatten $ to_simple $ tactic_state.pp_magic ts e in
    let m : sm  := sm.tag_expr [] e m in -- [hack] in pp.cpp I forgot to add an expr-boundary for the root expression.
    [ h "span" [
          className "expr",
          key e.hash,
          on_mouse_leave (λ _, action.on_mouse_leave_all) ] $ view tooltip_comp (prod.snd <$> ca) (prod.snd <$> sa) ⟨e, []⟩ m
      -- expr.address.to_string $ match ca with | none := [] | (some ⟨x,y⟩) := y end,
      -- expr.address.to_string $ match sa with | none := [] | (some ⟨x,y⟩) := y end
      ]
  )

/-- Render the implicit arguments for an expression in fancy, little pills. -/
meta def implicit_arg_list (ts : tactic_state) (tooltip : component (expr × expr.address) empty) (e : expr) : html empty :=
h "div" []
  ( (h "span" [className "bg-blue br3 ma1 ph2 white"] [html.of_component (expr.get_app_fn e) $ mk ts (tooltip)]) ::
    list.map (λ a, h "span" [className "bg-gray br3 ma1 ph2 white"] [html.of_component a $ mk ts (tooltip)]) (expr.get_app_args e)
  )

meta def type_tooltip (ts : tactic_state) : component (expr × expr.address) empty :=
component.stateless (λ ⟨e,ea⟩,
  match tactic.run_simple ts (do
    y ← tactic.infer_type e,
    pure [
        h "div" [] [
          h "div" [] [html.of_component y $ mk ts type_tooltip],
          h "hr" [] [],
          implicit_arg_list ts type_tooltip e,
          h "hr" [] [],
          h "div" [className "gray"] [
            ea.to_string
          ]
        ]
      ]
  ) with
  | none := "error getting type at " ++ (repr $ ea)
  | (some t) := t
  end
)

end interactive_expression

meta def html.of_name {α : Type} : name → html α
| n := html.of_string $ name.to_string n

open tactic

meta def tactic_render : tactic (html empty) := do
  gs ← get_goals,
  hs : list (html empty) ← gs.mmap (λ g, do
    ts ← read,
    gn ← pp g,
    set_goals [g],
    lcs ← local_context,
    lchs : list (html empty) ← lcs.mmap (λ lc, do
      pn ← pure $ expr.local_pp_name lc,
      y ← infer_type lc,
      pure
        $ h "tr" [key $ to_string $ expr.local_uniq_name lc] [
            h "td" [] [html.of_name pn],
            h "td" [] [html.of_string " : "],
            h "td" [] [html.of_component y $ interactive_expression.mk ts (interactive_expression.type_tooltip ts)]
        ]
    ),
    t ← target,
    pure $ h "table" [key $ expr.hash g, className "font-code"] [
      h "tbody" [] $ lchs ++ [
          h "tr" [] [
            h "td" [] (∅) ,
            h "td" [] [html.of_string " ⊢ "],
            h "td" [val "width" "100%"] $ html.of_component t $ interactive_expression.mk ts (interactive_expression.type_tooltip ts)
       ]]
    ]
  ),
  pure $ h "ul" [className "list pl0"]
       $ list.mapi (λ x i,
         let border_cn := if i + 1 = hs.length then "ba bl-0 bt-0 br-0 b--dotted b--black-30" else "" in
         h "li" [className $ "lh-copy " ++ border_cn] [x])
       $ hs

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

meta def tactic_state_widget : component tactic_state string :=
mk_tactic_widget () (λ _ _, failure) (λ _, tactic_render) (λ _ x, x)

end widget



