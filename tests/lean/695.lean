def with_zero (α) := option α
instance {α} [has_zero α] : has_zero (with_zero α) := ⟨none⟩
instance {α} : has_coe α (with_zero α) := ⟨some⟩

attribute [irreducible] with_zero

def segfault_please : with_zero ℕ → ℕ
| 0 := 0
| (n : ℕ) := n
