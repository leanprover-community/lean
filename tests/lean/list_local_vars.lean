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
do ls ← lean.parser.list_include_variables,
   (n,t) ← brackets "(" ")" (prod.mk <$> (ident <* tk ":") <*> texpr),
   t ← tactic.to_expr t,
   v ← tactic.mk_local_def n t,
   lean.parser.add_local v,
   (n',t') ← brackets "(" ")" (prod.mk <$> (ident <* tk ":") <*> texpr),
   t' ← tactic.to_expr t',
   v ← tactic.mk_local_def n' t',
   lean.parser.add_local v,
   trace ls,
   brackets "(" ")" texpr,
   ↑(ls.mmap' $ trace ∘ to_string)

end tactic.interactive
-- stuff 1
variables (a b c : ℕ)
include a b
variables {α : Type}
section
stuff (β : Type) (γ : Type) (α × β × γ)
def x := β

#check x
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
