meta def foo (x : reflected ℕ 3) : reflected (list ℕ) [10] :=
x -- ERROR

def synonym (α : Type) : Type := α

def synonym.of {α : Type} (a : α) : synonym α := a

meta instance synonym.reflect {α : Type} [h : has_reflect α] [reflected _ α] :
  has_reflect (synonym α) :=
λ x, show reflected _ (synonym.of x), from `(synonym.of).subst (h x)

run_cmd let x := synonym.of 1 in tactic.trace `(x)
run_cmd let x := 1 in tactic.trace `(x)
