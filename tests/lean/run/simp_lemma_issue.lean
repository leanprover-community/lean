universe variables u

class comm_semiring (α : Type*) extends has_zero α, has_add α, has_one α, has_mul α.

lemma zero_add {α : Type*} [comm_semiring α] (a : α) : (0:α) + a = a := sorry
lemma add_zero {α : Type*} [comm_semiring α] (a : α) : a + 0 = a := sorry

instance foo : comm_semiring nat :=
{ zero := 0, one := 1, add := (+), mul := (*) }

def ex {α : Type u} [comm_semiring α] (a : α) : 0 + a = a :=
zero_add a

-- local attribute [-simp] zero_add add_zero
attribute [simp] ex

example (a b : nat) : 0 + 0 + a = a :=
by simp

-- local attribute [-ematch] zero_add add_zero
attribute [ematch] ex

example (a b : nat) : 0 + 0 + a = a :=
by using_smt $ smt_tactic.eblast
