open tactic

instance aa : is_associative ℕ (+) := ⟨nat.add_assoc⟩
instance ac : is_commutative ℕ (+) := ⟨nat.add_comm⟩
instance ma : is_associative ℕ (*) := ⟨nat.mul_assoc⟩
instance mc : is_commutative ℕ (*) := ⟨nat.mul_comm⟩

example (a b c : nat) (f : nat → nat) : f (a + b + c) = f (c + b + a) :=
by cc

example (a b c : nat) (f : nat → nat) : a + b = c → f (c + c) = f (a + b + c) :=
by cc
