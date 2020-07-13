inductive trans_gen {α} (r : α → α → Prop) (a : α) : α → Prop
| single {b} : r a b → trans_gen b
| tail {b c} : trans_gen b → r b c → trans_gen c

def uncurry {α β γ} (f : α → β → γ) (p : α × β) : γ :=
f p.fst p.snd

def curry {α β γ} (f : α × β → γ) (a : α) (b : β) : γ :=
f (a, b)

def foo
  {α : Type}
  {r : α × α → Prop}
  {x : α × α}
  (h : uncurry (trans_gen (curry r)) x) :
  true :=
begin
  cases h,
  case tail : a b c { trivial },
  case single { trivial }
end
