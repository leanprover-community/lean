class ring (α : Type*) extends has_zero α.
constant {u} f {α : Type u} : α → α → α → α
axiom {u} fax {α : Type u} [ring α] (a b : α) : f a b a = 0

attribute [ematch] fax

universe variables u

class field (α : Type*) extends ring α, has_add α.

lemma ex {α : Type u} [field α] (x y : α) : f (x + y) (y + x) (x + y) = 0 :=
begin [smt] ematch end
