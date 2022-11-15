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
#check Π (m n : ℕ), ℤ
#check Π (m n : ℕ), fin m
#check Π (m n : ℕ), fin n
#check ∀ (m n : ℕ), 1 = 2
#check ∀ (m n : ℕ), m = 1
#check ∀ (m n : ℕ), n = 1
#check ∀ (m n : ℕ), m = n
#check ∀ (m : ℕ) (h : p), q ∧ m = 1
#check ∀ (m : ℕ) (h : p), q
#check ∀ (h : p) (m : ℕ), q ∧ m = 1
#check ∀ (h : p) (m : ℕ), q

section
-- A limitation due to use of relaxed weak head normal form:

#check let Prop' := Prop, not' (p : Prop') := ¬ p in ∀ (p : Prop'), p → not' p
-- shows ∀ (p : Prop') (_ : p), not' p

abbreviation Prop' := Sort 0
#check let not' (p : Prop') := ¬ p in ∀ (p : Prop'), p → not' p
-- shows ∀ (p : Prop'), p → not' p

end
