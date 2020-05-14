open tactic

instance aa : is_associative ℕ (+) := ⟨nat.add_assoc⟩
instance ac : is_commutative ℕ (+) := ⟨nat.add_comm⟩
instance ma : is_associative ℕ (*) := ⟨nat.mul_assoc⟩
instance mc : is_commutative ℕ (*) := ⟨nat.mul_comm⟩

example (a b c d e : nat) (f : nat → nat → nat) : b + a = d → b + c = e → f (a + b + c) (a + b + c) = f (c + d) (a + e) :=
by cc

example (a b c d e : nat) (f : nat → nat → nat) : b + a = d + d → b + c = e + e → f (a + b + c) (a + b + c) = f (c + d + d) (e + a + e) :=
by cc

section
  universe variable u
  variables {α : Type u}
  variables op : α → α → α
  variables [is_associative α op]
  variables [is_commutative α op]

  lemma ex (a b c d e : α) (f : α → α → α) : op b a = op d d → op b c = op e e → f (op a (op b c)) (op (op a b) c) = f (op (op c d) d) (op e (op a e)) :=
  by cc
end
