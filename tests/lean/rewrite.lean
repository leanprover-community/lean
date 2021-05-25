class is_one_class (n : ℕ) :=
(one : n = 1)

lemma one_eq (n : ℕ) [is_one_class n] : 1 = n := is_one_class.one.symm

-- error message should say which typeclass is missing
example (n : ℕ) : n = 1 := by rw one_eq
