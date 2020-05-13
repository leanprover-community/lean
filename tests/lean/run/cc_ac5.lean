universe variables u

class ring (α : Type u) extends has_mul α, has_add α :=
(add_comm : ∀ a b : α, a + b = b + a)
(add_assoc : ∀ a b c : α, a + b + c = a + (b + c))

variables {α : Type u}
variables [ring α]
open tactic

instance aa : is_associative α (+) := ⟨ring.add_assoc⟩
instance ac : is_commutative α (+) := ⟨ring.add_comm⟩
constant ma : is_associative α (*)
constant lc : is_left_cancel α (+)
constant rc : is_right_cancel α (+)
constant ld : is_left_distrib α (*) (+)
constant rd : is_right_distrib α (*) (+)

example (x1 x2 x3 x4 x5 x6 : α) : x1*x4 = x1 → x3*x6 = x5*x5 → x5 = x4 → x6 = x2 → x1 = x1*(x6*x3) :=
by cc

example (y1 y2 x2 x3 x4 x5 x6 : α) : (y1 + y2)*x4 = (y2 + y1) → x3*x6 = x5*x5 → x5 = x4 → x6 = x2 → (y2 + y1) = (y1 + y2)*(x6*x3) :=
by cc

example (y1 y2 y3 x2 x3 x4 x5 x6 : α) : (y1 + y2)*x4 = (y3 + y1) → x3*x6 = x5*x5 → x5 = x4 → x6 = x2 → y2 = y3 → (y2 + y1) = (y1 + y3)*(x6*x3) :=
by cc
