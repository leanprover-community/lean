/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
import init.function init.data.option.basic init.util

/- A component is a piece of UI which may contain internal state. Use component.mk to build new components.

## Using widgets.

The process is still less than streamlined.
To make a widget, you need to make a custom executor object and then instead of calling `save_info_thunk` you call `save_widget`.

Additionally, you will need a compatible build of the vscode extension or web app to use widgets in vscode.

## How it works:

The design is inspired by React, although the output is always an entire piece of html rather than a diff.
If you are familiar with using React or Elm or a similar functional UI framework then that's helpful for this.
The [React article on reconciliation](https://reactjs.org/docs/reconciliation.html) might be helpful.

Given an active document, Lean (in server mode) maintains a set of __widgets__ for the document.
A widget is a component `c`, some `p : Props` and an internal state-manager which manages the states of the component and subcomponents and also handles the routing of events from the UI.

When a widget is requested for rendering, `init p none` is called to create the first `s₀ : State`, then `view p s₀` is called to create an HTML tree `h`.
Recursively, for each nested component `c'` in the tree, this process is repeated until a pure html tree is generated which is then sent to the client for display.
This process is called __rendering__.

The client then displays this UI and the user may interact with it.
If the user clicks something, the client will send a message to the widget indicating that an action `a` was performed.
`update p s a` will then be called on the relevant subcomponent
resulting in a pair `⟨s,b⟩ : State × option Action`.

The component's state is replaced with `s`.
If `b` is `some x`,  the parent component's `update` will also be called with `x` and so on up the component tree.

Finally, the entire component is re-rendered to produce a new piece of html to send to the client for display.
On this rerendering, the new html and the old html are compared through a process called __reconciliation__.
Reconciliation will make sure that the states are carried over correctly and will also not rerender subcomponents if they haven't changed their props or state.
The reconciliation engine uses the `props_eq` predicate passed to the component constructor to determine whether the props have changed and hence whether the component should be re-rendered.

## Keys

If you have some list of components and the list changes according to some state, it is important to add keys to the components so
that if two components change order in the list their states are preserved.
If you don't provide keys or there are duplicate keys then you may get some strange behaviour in both the Lean widget engine and react.

## Further work:

Some things that would be interesting to implement and which may improve performance.

- instead of sending a whole html-tree each time, generate a patch that react can use to update
- how should style sheets work? right now you need to just use the styles provided by the client or use inline styles.
- timers, right now the round trip from client to server is too
- a top level action that allows the user to
- if `decidable_eq Props`, then reconciliation can compare the old and new props and check whether the given subcomponent needs to be re-rendered, possibly increasing efficiency.
- a parser from jsx-like expressions?!
- currently component and html both have to be implemented natively for universe issues, it would be really cool if they could be non-meta and expressed as lean inductive datatypes.

-/

namespace widget

inductive mouse_event_kind
| on_click
| on_mouse_enter
| on_mouse_leave

meta mutual inductive component, html, attr

with component : Type → Type → Type
|mk {Props : Type}
    {Action : Type}
    (InnerAction : Type)
    (State : Type)
    (init : Props → option State → State)
    (update : Props → State → InnerAction → State × option Action)
    (view : Props → State → list (html InnerAction))
    /- If this returns true, then the component will not call 'view' again. -/
    (props_eq : Props → Props → bool)
    : component Props Action

with html : Type → Type
| element      {α : Type} (tag : string) (attrs : list (attr α)) (children : list (html α)) : html α
| of_string    {α : Type} : string → html α
| of_component {α : Type} {Props : Type} : Props → component Props α → html α

with attr : Type → Type
| val               {α : Type} (name : string) (value : string) : attr α
| mouse_event       {α : Type} (kind : mouse_event_kind) (handler : unit → α) : attr α
| style             {α : Type} : list (string × string) → attr α
| tooltip           {α : Type} : html α → attr α
| text_change_event {α : Type} (handler : string → α) : attr α

variables {α β : Type} {π : Type}

namespace component

meta def filter_map_action (f : α → option β) : component π α → component π β
| (component.mk γ σ init update view props_are_eq) := component.mk γ σ init (λ p s b, let ⟨s,a⟩ := update p s b in ⟨s, a >>= f⟩) view props_are_eq

meta def map_action (f : α → β) : component π α → component π β
| c := filter_map_action (pure ∘ f) c

variables {ρ : Type}
meta def map_props (f : ρ → π) : component π α → component ρ α
| (component.mk γ σ init update view props_are_eq) := component.mk γ σ (init ∘ f) (update ∘ f) (view ∘ f) (props_are_eq on f)

meta def with_props_eq (e : π → π → bool) : component π α → component π α
| (component.mk γ σ init update view props_are_eq) := component.mk γ σ init update view e

meta def stateless [decidable_eq π] (view : π → list (html α)) : component π α :=
component.mk α unit (λ p _, ()) (λ p s b, ((), some b)) (λ p s, view p) (λ x y, x = y)

/-- Returns a component that will never trigger an action. -/
meta def ignore_action : component π α → component π β
| c := component.filter_map_action (λ a, none) c

meta def ignore_props : component unit α → component π α
| c := component.map_props (λ p, ()) c

meta instance : has_coe (component π empty) (component π α)
:= ⟨component.filter_map_action (λ x, none)⟩

meta def mk_simple [decidable_eq π] (β σ : Type) (init : σ) (update : π → σ → β → σ × option α) (view : π → σ → list (html β)) : component π α :=
component.mk β σ (λ x o, init <| o) update view (λ x y, x = y)

end component

meta mutual def attr.map_action, html.map_action (f : α → β)
with attr.map_action : attr α → attr β
| (attr.val k v) := attr.val k v
| (attr.style s) := attr.style s
| (attr.tooltip h) := attr.tooltip $ html.map_action h
| (attr.mouse_event k a) := attr.mouse_event k (f ∘ a)
| (attr.text_change_event a) := attr.text_change_event (f ∘ a)
with html.map_action : html α → html β
| (html.element t a c) := html.element t (list.map attr.map_action a) (list.map html.map_action c)
| (html.of_string s) := html.of_string s
| (html.of_component p c) := html.of_component p $ component.map_action f c

meta instance attr.is_functor : functor attr :=
{ map := @attr.map_action }

meta instance html.is_functor : functor html :=
{ map := λ _ _, html.map_action }

namespace html

meta instance to_string_coe [has_to_string β] : has_coe β (html α) :=
⟨html.of_string ∘ to_string⟩

meta instance : has_emptyc (html α) := ⟨of_string ""⟩

meta instance list_coe : has_coe (html α) (list (html α)) := ⟨λ x, [x]⟩

end html

meta def as_element : html α → option (strng × list (attr α) × list (html α))
| (html.element t a c) := some ⟨t,a,c⟩
| _ := none

meta def key [has_to_string β] : β → attr α
| s := attr.val "key" $ to_string s

meta def className : string → attr α
| s := attr.val "className" $ s

meta def on_click : (unit → α) → attr α
| a := attr.mouse_event mouse_event_kind.on_click a

meta def on_mouse_enter : (unit → α) → attr α
| a := attr.mouse_event mouse_event_kind.on_mouse_enter a

meta def on_mouse_leave : (unit → α) → attr α
| a := attr.mouse_event mouse_event_kind.on_mouse_leave a

/-- Alias for `html.element`. -/
meta def h : string → list (attr α) → list (html α) → html α := html.element
/-- Alias for className. -/
meta def cn : string → attr α := className

meta def button : string → thunk α → html α
| s t := h "button" [on_click t] [s]

meta def textbox : string → (string → α) → html α
| s t := h "input" [attr.val "type" "text", attr.val "value" s, attr.text_change_event t] []

/-- If the html is not an of_element it will wrap it in a div. -/
meta def with_attrs : list (attr α) →  html α → html α
| a x := match as_element x with
         | (some ⟨t,as,c⟩) := html.element t (a ++ as) c
         | none := html.element "div" a [x]
         end

/-- If the html is not an of_element it will wrap it in a div. -/
meta def with_attr : attr α →  html α → html α
| a x := with_attrs [a] x

meta def with_style : string → string → html α → html α
| k v h := with_attr (attr.style [(k,v)]) h

meta def with_cn : string → html α → html α
| s h := with_attr (className s) h

meta def with_key {β} [has_to_string β] : β → html α → html α
| s h := with_attr (key s) h

end widget

/-- Same as `tactic.save_info_thunk` except saves a widget to be displayed by a compatible infoviewer. -/
meta constant tactic.save_widget : pos → widget.component tactic_state string → tactic unit
