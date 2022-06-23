meta def eval_list (α : Type) [reflected _ α] (e : expr) : tactic (list α) :=
tactic.eval_expr (list α) e

run_cmd eval_list ℕ ↑`([1, 2]) >>= tactic.trace

def synonym (α : Type) : Type := α

def synonym.of {α : Type} (a : α) : synonym α := a

meta instance synonym.reflect {α : Type} [has_reflect α] [reflected α] :
  has_reflect (synonym α) :=
λ x, show reflected (synonym.of x), from `(synonym.of).subst `(x)

#eval let x := synonym.of 1 in tactic.trace `(x)
