variables (p q : Prop)
#check p → q
#check p → ℕ
#check ℕ → p
#check ℕ → ℕ
#check ℕ → Prop
#check ℕ → Type
#check ∀ (n : ℕ), n > 0
#check ∀ (n : ℕ), 1 = 2
#check Π (n : ℕ), ℤ
#check Π {n : ℕ}, ℤ
#check Π (n : ℕ), fin n
#check ∀ n : ℕ, ¬∃ x : ℕ, x ≠ x
