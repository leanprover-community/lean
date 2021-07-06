universe u

instance {α : Type u} : has_coe_to_sort (set α) (Type u) := ⟨λ s, {x // x ∈ s}⟩

example : ↥({0} : set ℕ) := ⟨0, rfl⟩