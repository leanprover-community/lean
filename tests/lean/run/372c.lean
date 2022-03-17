def foo (n : ℕ) := Type
def beta (n : ℕ) : foo n :=
by unfold foo; exact ℕ → ℕ
noncomputable lemma baz (n : ℕ) : beta n := id
example : ℕ := by apply baz <|> exact 0
