/- Authors: E.W.Ayers -/
prelude
import init.data
namespace native
/- [TODO](easy) replace this with the IEEE specification of floats.  -/
meta constant float : Type
namespace float
meta constant add : float → float → float
meta instance : has_add float := ⟨add⟩
meta constant sub : float → float → float
meta instance : has_sub float := ⟨sub⟩
meta constant mul : float → float → float
meta instance : has_mul float := ⟨mul⟩
meta constant div : float → float → float
meta instance : has_div float := ⟨div⟩
meta constant neg : float → float
meta instance : has_neg float := ⟨neg⟩
meta constant pow : float → float → float
meta instance : has_pow float float := ⟨pow⟩
/-- Natural logarithm. -/
meta constant log : float → float 
meta constant of_nat : nat → float
meta constant of_int : int → float
meta instance of_nat_coe : has_coe nat float := ⟨of_nat⟩
meta instance of_int_coe : has_coe int float := ⟨of_int⟩
meta constant to_repr : float → string
meta instance : has_repr float := ⟨to_repr⟩
meta instance : has_to_string float := ⟨to_repr⟩
meta instance : has_to_format float := ⟨format.of_string ∘ to_string⟩
meta instance : has_one float := ⟨of_nat 1⟩
meta instance : has_zero float := ⟨of_nat 0⟩
meta constant lt : float → float → bool
meta instance : has_lt float := ⟨λ x y, lt x y⟩
meta instance : decidable_rel (float.has_lt.lt) := by apply_instance
meta constant dec_eq : decidable_eq float
meta constant abs : float → float
attribute [instance] dec_eq

meta constant pi : float
meta constant sin : float → float
meta constant cos : float → float
meta constant tan : float → float
meta constant sinh : float → float
meta constant cosh : float → float
meta constant tanh : float → float
meta constant asin : float → float
meta constant acos : float → float
meta constant atan : float → float
/-- `atan2 y x` finds the angle anticlockwise from the x-axis to the point `[x,y]`.-/
meta constant atan2 : float → float → float

meta constant exp : float → float
meta constant sqrt : float → float

meta constant ceil : float → float
meta constant floor : float → float

end float
end native