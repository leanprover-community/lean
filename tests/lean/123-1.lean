/-- notation typeclass not in core.  -/
class has_scalar (G : Type) (V : Type) := (smul : G → V → V)

infixr ` • `:73 := has_scalar.smul

structure Ring : Type.

instance : has_coe_to_sort Ring Type :=
⟨λ R, unit⟩

variables {G : Type} [has_mul G] {R : Ring}

class distrib_mul_action' (G : Type) (V : Type)
  [has_mul G]
  extends has_scalar G V :=
(foo : ∀ (x y : G) (b : V), x • b = x • y • b) -- note that changing x • y • b to y • b fixes the violation
                                               -- and instead we get a different error.

structure finsupp' (β : Type) : Type :=
(to_fun             : β → β)

def mas (r : R) : finsupp' ↥R  :=
{
  to_fun := id,
}

variables (V : Type)

instance foo : distrib_mul_action' G V :=
{
  smul := λ g v, (mas ()) • v, -- note that changing () to 37 also causes an assertion violation
  foo := λ g g' v, sorry
}
