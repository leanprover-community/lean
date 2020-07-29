variables {α : Type} [has_one α]
#check {(1 : α)}
#check {(1), (2), (3)}
#check ({(∘), (∘)} : set ((ℕ → ℕ) → (ℕ → ℕ) → (ℕ → ℕ)))