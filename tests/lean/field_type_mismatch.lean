namespace test

instance : has_add nat :=
{add := nat.succ}

class semigroup (α : Type) extends has_mul α :=
(mul_assoc : ∀ x y z : α, x * y * z = x * (y * z))

instance : semigroup nat :=
{mul       := nat.add,
 mul_assoc := trivial }

end test
