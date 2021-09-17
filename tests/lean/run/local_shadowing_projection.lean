instance : has_lt (nat × nat) := { lt := λ a b, a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 < b.2 }

def prod.cmp (a b : nat × nat) : ordering :=
cmp a b

namespace prod
  def foo (a : nat × nat) (cmp : nat) :=
  a.cmp
end prod
