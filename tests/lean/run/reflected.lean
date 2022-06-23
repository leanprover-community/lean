meta def eval_list (α : Type) [reflected _ α] (e : expr) : tactic (list α) :=
tactic.eval_expr (list α) e

run_cmd eval_list ℕ ↑`([1, 2]) >>= tactic.trace

def synonym (α : Type) : Type := α

def synonym.of {α : Type} (a : α) : synonym α := a

meta instance synonym.reflect {α : Type} [h : has_reflect α] [reflected _ α] :
  has_reflect (synonym α) :=
λ x, show reflected _ (synonym.of x), from `(synonym.of).subst (h x)

run_cmd let x := synonym.of 1 in tactic.trace `(x)
run_cmd let x := 1 in tactic.trace `(x)
