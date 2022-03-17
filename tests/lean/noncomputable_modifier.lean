import init.meta.interactive

open tactic lean lean.parser interactive

meta def describe_it : noncomputable_modifier → string
| noncomputable_modifier.computable := "computable"
| noncomputable_modifier.noncomputable := "noncomputable"
| noncomputable_modifier.force_noncomputable := "force_noncomputable"

@[user_command] meta def my_command (mi : interactive.decl_meta_info)
  (_ : parse (tk "my_command")) : parser unit := do
trace $ describe_it mi.modifiers.is_noncomputable
.

my_command

noncomputable
my_command

noncomputable!
my_command

def n1 : ℕ := 37
#eval n1
noncomputable def n2 : ℕ := 37
#eval n2
noncomputable! def n3 : ℕ := 37
#eval n3

noncomputable theory
noncomputable def n4 : ℕ := 37
#eval n4
noncomputable! def n5 : ℕ := 37
#eval n5
noncomputable! theory
