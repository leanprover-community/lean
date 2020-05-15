universe variables u

class comm_ring (α : Type u) extends has_mul α, has_add α, has_zero α, has_one α.

variables {α : Type u}
variables [comm_ring α]
open tactic

instance aa : is_associative α (+) := ⟨sorry⟩
instance ac : is_commutative α (+) := ⟨sorry⟩
instance ma : is_associative α (*) := ⟨sorry⟩
instance mc : is_commutative α (*) := ⟨sorry⟩
instance lc : is_left_cancel α (+) := ⟨sorry⟩
instance rc : is_right_cancel α (+) := ⟨sorry⟩
instance ld : is_left_distrib α (*) (+) := ⟨sorry⟩
instance rd : is_right_distrib α (*) (+) := ⟨sorry⟩
instance l0a : is_left_id α (*) 0 := ⟨sorry⟩
instance r0a : is_right_id α (*) 0 := ⟨sorry⟩
instance l0m : is_left_null α (*) 0 := ⟨sorry⟩
instance r0m : is_right_null α (*) 0 := ⟨sorry⟩

example (x1 x2 x3 x4 x5 x6 : α) : x1*x4 = x1 → x3*x6 = x5*x5 → x5 = x4 → x6 = x2 → x1 = x1*(x6*x3) :=
by cc

example (y1 y2 x2 x3 x4 x5 x6 : α) : (y1 + y2)*x4 = (y2 + y1) → x3*x6 = x5*x5 → x5 = x4 → x6 = x2 → (y2 + y1) = (y1 + y2)*(x6*x3) :=
by cc

example (y1 y2 y3 x2 x3 x4 x5 x6 : α) : (y1 + y2)*x4 = (y3 + y1) → x3*x6 = x5*x5 → x5 = x4 → x6 = x2 → y2 = y3 → (y2 + y1) = (y1 + y3)*(x6*x3) :=
by cc
