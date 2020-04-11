

inductive html.attr (α : Type) : Type
| val (name : string) (value : string) : html.attr
| on_click : (unit → α) → html.attr
| style : list (string × string) → html.attr
-- | on_mouse : (mouse_event_args → α) → html.attr
-- [todo] more coming...

inductive html (α : Type) : Type
| element : string → list (attr α) → html → html
| of_string : string → html
| empty : html
| append : html→ html→ html

namespace html

variables {α β : Type}

instance string_coe : has_coe string (html α) := ⟨html.of_string⟩

instance : has_append (html α) := ⟨html.append⟩

instance : has_emptyc (html α) := ⟨html.empty⟩

def of_list : (list (html α)) → html α := list.foldl (++) ∅

instance list_coe : has_coe (list (html α)) (html α) := ⟨of_list⟩

def button : string → thunk α → html α
| s t := html.element "button" [attr.on_click t] s

def div : list (html α) →  html α
| l := element "div" [] l

namespace attr

protected def map (f : α → β) : attr α → attr β
| (attr.on_click a) := attr.on_click (f ∘ a)
| (attr.val k v) := attr.val k v
| (attr.style s) := attr.style s

instance is_functor : functor attr :=
{ map := @attr.map }

end attr

protected def map (f : α → β) : html α → html β
| (element s as c) := (element s (list.map (attr.map f) as) $ map c)
| (of_string s) := of_string s
| (empty) := empty
| (append l r) := append (map l) (map r)

instance is_functor : functor (html) :=
{ map := @html.map }

end html