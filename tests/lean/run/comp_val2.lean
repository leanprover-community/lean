open tactic

example : 'a' ≠ 'b' := by comp_val
example : '0' ≠ 'a' := by comp_val

example : "hello worlg" ≠ "hhello world" := by comp_val
example : "hello world" ≠ "hhello world" := by comp_val
example : "abc" ≠ "cde" := by comp_val
example : "abc" ≠ "" := by comp_val
example : "" ≠ "cde" := by comp_val

example : (⟨3, dec_trivial⟩ : fin 5) ≠ ⟨4, dec_trivial⟩ :=
by comp_val

example : (⟨4, dec_trivial⟩ : fin 5) ≠ ⟨1, dec_trivial⟩ :=
by comp_val

example {P : ℕ → Prop} {h1 : P 1} {h5 : P 5} :
  (⟨1, h1⟩ : {n // P n}) ≠ ⟨5, h5⟩ :=
by comp_val
