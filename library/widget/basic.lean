
/-- A component is a piece of UI which may contain internal state. Use component.mk to build new components.

`component` is effectively implemented as

```
structure component (Props Action : Type) :=
(InnerAction : Type)
(State : Type)
(init : Props → option State → State)
(update : Props → State → InnerAction → State × option Action)
(view : Props → State → html InnerAction)
```

However the type parameters mean that it has to be implemented natively or the universe is too large.

## Using widgets.

The process is still less than streamlined.
To make a widget, you need to make a custom executor object and then instead of calling `save_info_thunk` you call `save_widget`.

Additionally, you will need a special build of the vscode extension [todo] to use widgets in vscode.

The html is sent as a json object and rendered using React, so I don't think you can make a script injection attack.

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

## Keys

If you have some list of components and the list changes according to some state, it is important to add keys to the components so
that if two components change order in the list their states are preserved.

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
meta constant component (Props : Type) (Action : Type) : Type

/-- `html` represents an abstract piece of html markup which may have nested `component`s.
If universe / mutual induction issues were not a problem, the non-native definition would be:

```
inductive html (Action : Type) : Type
| of_element : element Action → html
| of_string : string → html
| of_component : Π {Props : Type} → Props → component Props Action → html
```
-/
meta constant html (Action : Type) : Type

meta constant tactic.save_widget {α : Type} : pos → component tactic_state α → tactic unit

inductive mouse_event_kind
| on_click
| on_mouse_enter
| on_mouse_leave

/-- An attribute for an html element. For example the `id="mydiv"` in `<div id="mydiv"/>`. React conventions are used.  -/
meta inductive html.attr (Action : Type) : Type
| val (name : string) (value : string) : html.attr
| mouse_event : mouse_event_kind → (unit → Action) → html.attr
| style : list (string × string) → html.attr -- [NOTE] multiple style attributes will get merged.
/-- If this is set, then a popper will render containing the given content pointing to this element. -/
| tooltip : html Action → html.attr
/-- For use with textboxes, otherwise it won't fire. -/
| text_change_event : (string → Action) → html.attr
-- [todo] more coming...
-- drop_target : ()


meta structure html.element (α : Type) : Type :=
(tag : string)
(attributes : list (attr α))
(children : list (html α))

variables {α : Type}
meta constant html.of_element : html.element α → html α
meta constant html.of_string : string → html α
meta constant html.of_component {π : Type} : π → component π α → html α

protected meta constant html.cases {C : Type}
  (element : html.element α → C)
  (string : string → C)
  (component : Π (π : Type), π → component π α → C)
 : html α → C

variables {π : Type}

meta constant component.mk
  -- [decidable_eq π] -- [todo] for fast reconciling.
  (β σ : Type)
  (init : π → option σ → σ)
  (update : π → σ → β → σ × option α)
  (view : π → σ → list (html β))
  : component π α

meta constant component.state : component π α → Type
meta constant component.event : component π α → Type
meta constant component.init (c : component π α) : (π → option (c.state) → (c.state))
meta constant component.update (c : component π α) : (π → c.state → c.event → c.state × option α)
meta constant component.view (c : component π α) : (π → c.state → list (html c.event))

namespace component

meta def filter_map_action {π α β : Type} (f : α → option β) : component π α → component π β
| c := mk c.event c.state c.init (λ p s b, let ⟨s,a⟩ := c.update p s b in ⟨s, a >>= f⟩) c.view

meta def map_action {π α β : Type} (f : α → β) : component π α → component π β
| c := filter_map_action (pure ∘ f) c

meta def map_props  {π ρ α : Type} (f : ρ → π) : component π α → component ρ α
| c := component.mk c.event c.state (c.init ∘ f) (c.update ∘ f) (c.view ∘ f)

meta def stateless {π : Type} (view : π → list (html α)) : component π α :=
component.mk α unit (λ p _, ()) (λ p s b, ((), some b)) (λ p s, view p)

end component
