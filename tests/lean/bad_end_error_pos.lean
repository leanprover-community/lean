example (a b : nat) (f : nat → nat) : f (a + b) = f (b + a) :=
by rw nat.add_comm

example (a b : nat) (f : nat → nat) : f (a * b) = f (b * a) :=
by rw nat.mul_comm

end

example (a b c : nat) (f : nat → nat → nat) : f (b * c) (a * b * c) = f (c * b) (a * (b * c)) :=
by rw [nat.mul_assoc, nat.mul_comm]
