def foo : ℕ → ℕ
| 0 := 1
| (n+1) := match n with 0 := 2 | _ := 1 end

lemma foo.faux_eqn (n) : foo n = 42 := sorry

open tactic
run_cmd do
e ← get_env,
trace $ e.get_eqn_lemmas_for ``foo,
trace $ e.get_ext_eqn_lemmas_for ``foo,
set_env $ e.add_eqn_lemma ``foo.faux_eqn

#eval do
e ← get_env,
trace $ e.get_eqn_lemmas_for ``foo,
trace $ e.get_ext_eqn_lemmas_for ``foo

-- success: we've taught lean a new and exciting simp lemma!
example : ∀ n, foo n = 42 := by simp [foo]