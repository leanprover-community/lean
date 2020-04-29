/- Some helpers for html. -/

import widget.basic

variables {π α : Type}

meta def html.as_element : html α → option (html.element α) := html.cases some (λ _, none) (λ _ _ _, none)

namespace html

open html
variables {β γ : Type}

section
variable (f : α → β)
meta mutual def attr.map_action, map_action, element.map_action
with attr.map_action  : attr α → attr β
| (attr.val k v) := attr.val k v
| (attr.style s) := attr.style s
| (attr.tooltip h) := attr.tooltip $ map_action h
| (attr.mouse_event k a) := attr.mouse_event k (f ∘ a)
| (attr.text_change_event a) := attr.text_change_event (f ∘ a)
with map_action : html α → html β
| h := html.cases
  (λ e, html.of_element $ element.map_action e)
  (λ s, html.of_string s)
  (λ π p c, html.of_component p $ component.map_action f c)
  h
with element.map_action : element α → element β
| ⟨t, as, cs⟩ := element.mk t (list.map attr.map_action as) (list.map map_action cs)
end

meta instance attr.is_functor : functor attr :=
{ map := @html.attr.map_action }

meta instance is_functor : functor (html) :=
{ map := λ _ _, html.map_action }

local notation `H` := html α

meta instance string_coe : has_coe string H := ⟨html.of_string⟩
meta instance to_string_coe [has_to_string β] : has_coe β H := ⟨html.of_string ∘ to_string⟩

meta instance : has_emptyc H := ⟨of_string ""⟩

meta instance list_coe : has_coe H (list H) := ⟨λ x, [x]⟩

namespace attr

meta def key [has_to_string β] : β → html.attr α
| s := html.attr.val "key" $ to_string s

meta def className : string → html.attr α
| s := html.attr.val "className" $ s

meta def on_click : (unit → α) → html.attr α
| a := html.attr.mouse_event mouse_event_kind.on_click a

meta def on_mouse_enter : (unit → α) → html.attr α
| a := html.attr.mouse_event mouse_event_kind.on_mouse_enter a

meta def on_mouse_leave : (unit → α) → html.attr α
| a := html.attr.mouse_event mouse_event_kind.on_mouse_leave a


end attr

meta def h (tag : string) (attributes : list (html.attr α)) (children : list (html α)) :=
html.of_element $ element.mk tag attributes children

meta def button : string → thunk α → H
| s t := h "button" [html.attr.on_click t] [s]

meta def textbox : string → (string → α) → H
| s t := h "input" [html.attr.val "type" "text", html.attr.val "value" s, attr.text_change_event t] []

meta def div : list H →  H
| l := h "div" [] l

meta def span : list H → H
| l := h "span" [] l

meta def td :  H  → H
| x := h "td" [] [x]

meta def th : H → H
| x := h "th" [] [x]

meta def tr : list H → H
| l := h "tr" [] l

meta def li : H → H
| l := h "li" [] [l]

meta def mk_headerless_table : list (list H) → H
| l := h "table" [] $ list.map (λ r, tr $ list.map td $ r) l

meta def element.with_attrs : list (html.attr α) → element α → element α
| as1 ⟨t, as2, c⟩ := ⟨t, as2 ++ as1, c⟩ -- [note] later attrs clobber earlier ones.

meta def element.with_attr : html.attr α → element α → element α
| a e := element.with_attrs [a] e

/-- If the html is not an of_element it will wrap it in a div. -/
meta def with_attr : html.attr α →  html α → html α
| a x := match as_element x with
         | (some e) := html.of_element $ element.with_attr a e
         | none := h "div" [a] [x]
         end

meta def with_style : string → string → H → H
| k v h := with_attr (attr.style [(k,v)]) h

meta def with_classname : string → H → H
| s h := with_attr (attr.val "className" s) h

meta def with_key : string → H → H
| s h := with_attr (attr.val "key" s) h

end html

