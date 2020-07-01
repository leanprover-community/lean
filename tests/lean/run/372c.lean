def foo (n : ℕ) := Type
def beta (n : ℕ) : foo n :=
by unfold foo; exact ℕ → ℕ
lemma baz (n : ℕ) : beta n := id
example : ℕ := by apply baz