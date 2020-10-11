variables {α : Type} [has_one α]
#check {(1 : α)}
#check {(1), (2), (3)}
#check ({(∘), (∘)} : set ((ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ)))

#check {(0) + (0)}

variables (a : α) [has_add α]
#check {(a)}
#check λ a, (by exact {(a)} : set α)
#check {(a + b) | b ∈ (∅ : set α)}
#check λ a, by exact {(a + b) | b ∈ (∅ : set α)}

#check {(prod.mk 1 2).fst}
#check {(prod.mk 1 b).fst | b ∈ ∅}