instance {α} : has_union (set α) := ⟨λ s t, {a | a ∈ s ∨ a ∈ t}⟩
constant union_is_assoc {α} : is_associative (set α) (∪)
attribute [instance] union_is_assoc

#check ({} : set nat)

open tactic expr

meta def is_assoc_bin_app : expr → tactic (expr × expr)
| (app (app op a1) a2) := do h ← to_expr ``(is_associative.assoc %%op), return (op, h)
| _                    := failed

#eval to_expr ``(({} : set nat) ∪ {}) >>= is_assoc_bin_app >>= λ p, trace p.2
