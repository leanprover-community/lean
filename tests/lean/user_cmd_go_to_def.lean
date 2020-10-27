open lean
open lean.parser
open interactive
open tactic

@[user_command]
meta def foo_cmd (_ : parse $ tk "mk_foo") : parser unit :=
add_decl $ declaration.defn `foo [] `(ℕ) `(42) reducibility_hints.abbrev tt.

 mk_foo

-- should be at the line of `mk_foo`
#eval (flip environment.decl_pos ``foo <$> tactic.get_env) >>= tactic.trace