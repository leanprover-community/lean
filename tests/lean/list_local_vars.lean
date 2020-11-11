-- #exit
open interactive tactic.interactive

namespace tactic.interactive
open lean.parser

meta def tac (ls : parse lean.parser.list_include_var_names) : tactic unit :=
trace ls

open interactive.types
@[user_command]
meta def tac_cmd (_ : parse $ tk "stuff") : lean.parser unit :=
with_local_scope $
do ls ← lean.parser.list_available_include_vars,
   trace ls,
   ls ← lean.parser.list_include_var_names,
   (n,t) ← brackets "(" ")" (prod.mk <$> (ident <* tk ":") <*> texpr),
   t ← tactic.to_expr t,
   v ← tactic.mk_local_def n t,
   lean.parser.add_local v,
   (n',t') ← brackets "(" ")" (prod.mk <$> (ident <* tk ":") <*> texpr),
   t' ← tactic.to_expr t',
   v ← tactic.mk_local_def n' t',
   lean.parser.add_local v,
   include_var v.local_pp_name,
   trace ls,
   ls ← tactic.local_context,
   trace ls,
   brackets "(" ")" texpr,
   ↑(ls.mmap' $ trace ∘ to_string)

@[user_command]
meta def add_var_cmd (_ : parse $ tk "add_var") : lean.parser unit :=
do (n,t) ← brackets "(" ")" (prod.mk <$> (ident <* tk ":") <*> texpr),
   t ← tactic.to_expr t,
   v ← tactic.mk_local_def n t,
   add_local_level `u,
   lean.parser.add_local v,
   include_var v.local_pp_name,
   (n',t') ← brackets "(" ")" (prod.mk <$> (ident <* tk ":") <*> texpr),
   t' ← tactic.to_expr t',
   v ← tactic.mk_local_def n' t',
   lean.parser.add_local v,
   include_var v.local_pp_name,
   omit_var v.local_pp_name,
   ls ← lean.parser.list_include_var_names,
   --  trace ls,
   trace_state

end tactic.interactive
variables (a b c : ℕ)
include a b
variables {α : Type}
section
stuff (β : Type) (γ : Type) (α × β × γ)
def x := β
def y := γ
#check x
section
add_var (β : Type) (γ : Type u)
def x' : β → β := id
def y' : γ → γ := id
end
def x'' := β
def y'' := γ
#check x'
#check y'
section
parameter δ : Type

#print δ
#print β
end
#print γ

end

example : c ≤ 3 :=
begin
  (do v ← tactic.get_local `a,
      trace $ v.local_pp_name ),
  tac
end
