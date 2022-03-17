constant foo : ℕ

noncomputable def bar : ℕ := foo

noncomputable lemma bar' : ℕ := 37

def baz : ℕ := 0

open tactic
run_cmd do
  e ← get_env,
  trace $ e.decl_noncomputable_reason `foo,
  trace $ e.decl_noncomputable_reason `bar,
  trace $ e.decl_noncomputable_reason `bar',
  trace $ e.decl_noncomputable_reason `baz
