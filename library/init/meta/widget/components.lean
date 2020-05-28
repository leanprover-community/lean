/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import init.meta.widget.tactic_component
import init.meta.interactive init.meta.derive
import init.data.punit
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

/-- A component which displays a tooltip when hovering over it. -/
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

end widget