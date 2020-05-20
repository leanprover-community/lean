instance aa : is_associative ℕ (+) := ⟨nat.add_assoc⟩
instance ac : is_commutative ℕ (+) := ⟨nat.add_comm⟩
instance ma : is_associative ℕ (*) := ⟨nat.mul_assoc⟩
instance mc : is_commutative ℕ (*) := ⟨nat.mul_comm⟩

example (a b c : nat) (f : nat → nat) : f (a + b + c) = f (b + c + a) :=
by ac_refl

example (a b c : nat) (f : nat → nat) : f (a + b + (c * b * a)) = f (b + (a * c * b) + a) :=
by ac_refl

example (a b c : nat) (f : nat → nat → nat) : f (b * c) (c * b * a) = f (c * b) (a * c * b) :=
by ac_refl

example (a b c : nat) (f : nat → nat) : f (a + (b * c) + (c * b * a)) = f ((c * b) + (a * c * b) + a) :=
by ac_refl

example (a b c : nat) (f : nat → nat) (g : nat → nat → nat) : g (f (a + (b * c) + (c * b * a))) (a + c + b + a) = g (f ((c * b) + (a * c * b) + a)) (c + b + a + a) :=
by ac_refl
