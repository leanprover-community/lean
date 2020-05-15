instance aa : is_associative ℕ (+) := ⟨nat.add_assoc⟩
instance ac : is_commutative ℕ (+) := ⟨nat.add_comm⟩
instance ma : is_associative ℕ (*) := ⟨nat.mul_assoc⟩
instance mc : is_commutative ℕ (*) := ⟨nat.mul_comm⟩

example (a b c : nat) (f : nat → nat → nat) : f (b * c) (c * b * a) = f (c * b) (a * c * b) :=
by ac_refl
