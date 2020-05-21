-- should fail
inductive foo : Type → Type
| mk : Π (α β : Type), (β → α) → foo α

-- should be fine
meta inductive foom : Type → Type
| mk : Π (α β : Type), (β → α) → foom α

