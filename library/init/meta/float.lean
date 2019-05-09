/- Authors: E.W.Ayers -/
prelude
import init.data
namespace native

meta constant float : Type
namespace float

-- fixed values based on the underlying C++ float implementation.
namespace specification
    /-- The base. Either 2 or 10. -/
    meta constant radix : nat
    /-- The length of the mantissa. -/
    meta constant precision : nat
    /-- The maximum exponent. -/
    meta constant emax : nat
    /-- The minimum exponent. `= 1 - emax` -/
    meta constant emin : int
end specification


meta constant epsilon : float
meta constant infinity : float
meta constant is_infinite : float → bool
meta constant is_finite : float → bool
meta constant is_nan : float → bool
meta constant is_normal : float → bool

/-- Quiet NaN. -/
meta constant qNaN : float
/-- Signalling NaN. -/
meta constant sNaN : float
/-- The sign `s` of the float. `tt` if negative. -/
meta constant sign : float → bool
/-- The exponent `e` of the float in the base given by `specification.radix`. `emin ≤ e ≤ emax`.  -/
meta constant exponent : float → int
/-- List of digits in the mantissa of the float. `d₀.d₁d₂d₃ ⋯`
    The length is `precision` and `0 ≤ dᵢ < radix` for each digit `dᵢ`.
    The head of the list is the most significant digit.
     -/
meta constant mantissa : float → array specification.precision nat

meta constant add : float → float → float
meta instance : has_add float := ⟨add⟩
meta constant sub : float → float → float
meta instance : has_sub float := ⟨sub⟩
meta constant neg : float → float
meta instance : has_neg float := ⟨neg⟩
meta constant mul : float → float → float
meta instance : has_mul float := ⟨mul⟩
meta constant div : float → float → float
meta instance : has_div float := ⟨div⟩

meta constant pow : float → float → float
meta instance : has_pow float float := ⟨pow⟩
meta constant sqrt : float → float
/-- Exponential function. -/
meta constant exp : float → float
/-- Natural logarithm. -/
meta constant log : float → float

meta constant pi : float

meta constant sin : float → float
meta constant cos : float → float
meta constant tan : float → float

meta constant asin : float → float
meta constant acos : float → float
meta constant atan : float → float
/-- `atan2 y x` finds the angle anticlockwise from the x-axis to the point `[x,y]`.-/
meta constant atan2 : float → float → float

meta constant sinh : float → float
meta constant cosh : float → float
meta constant tanh : float → float

meta constant abs : float → float
meta constant ceil : float → float
meta constant floor : float → float

meta constant lt : float → float → bool
meta instance : has_lt float := ⟨λ x y, lt x y⟩
meta instance : decidable_rel (float.has_lt.lt) := by apply_instance
meta constant dec_eq : decidable_eq float
attribute [instance] dec_eq

meta constant of_nat : nat → float
meta constant of_int : int → float
meta instance of_nat_coe : has_coe nat float := ⟨of_nat⟩
meta instance of_int_coe : has_coe int float := ⟨of_int⟩
meta instance : has_zero float := ⟨of_nat 0⟩
meta instance : has_one float := ⟨of_nat 1⟩

meta constant to_repr : float → string
meta instance : has_repr float := ⟨to_repr⟩
meta instance : has_to_string float := ⟨to_repr⟩
meta instance : has_to_format float := ⟨format.of_string ∘ to_string⟩

end float
end native