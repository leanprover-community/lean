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
open specification

/-- Returns the difference between 1.0 and the next representable value of the given floating-point type.
    Reference: https://en.cppreference.com/w/cpp/types/numeric_limits/epsilon
 -/
meta constant epsilon : float
/-- returns the maximum rounding error -/
meta constant round_error : float
/-- Positive infinity. -/
meta constant infinity : float
/-- Quiet NaN. -/
meta constant qNaN : float
/-- Signalling NaN. -/
meta constant sNaN : float
/-- Returns true when the value is positive or negative infinity.-/
meta constant is_infinite : float → bool
meta constant is_finite : float → bool
/-- Returns true when the value is qNaN or sNaN-/
meta constant is_nan : float → bool
/-- Reference: https://en.cppreference.com/w/cpp/numeric/math/isnormal
    https://stackoverflow.com/questions/8341395/what-is-a-subnormal-floating-point-number
-/
meta constant is_normal : float → bool
/-- The sign `s` of the float. `tt` if negative. -/
meta constant sign : float → bool
/-- The exponent `e` of the float in the base given by `radix`. `emin ≤ e ≤ emax`. Returns none if the number is not finite.  -/
meta constant exponent : float → option int
/-- Decompose the number `f` in to `(s,e)` where `0.5 ≤ s < 1.0` and `emin ≤ e ≤ emax` such that `f = s * 2 ^ e`. -/
meta constant frexp : float → float × int
/-- Decompose in to integer `fst` and fractional `snd` parts. -/
meta constant modf : float → float × float
/-- `mantissa f` returns a number `s` where `0.5 ≤ s < 1.0` such that there exists an integer `e` such that `f = s * 2 ^ e` -/
meta def mantissa : float → float := prod.fst ∘ frexp
-- [TODO]
-- /-- List of digits in the mantissa of the float. `d₀.d₁d₂d₃ ⋯`
--     The length is `precision` and `0 ≤ dᵢ < radix` for each digit `dᵢ`.
--     The head of the list is the most significant digit.
--      -/
-- meta constant mantissa_digits : float → array precision nat

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

/-- remainder of the floating point division operation. -/
meta constant fmod : float → float → float
/-- signed remainder of the division operation. -/
meta constant remainder : float → float → float

meta constant max : float → float → float
meta constant min : float → float → float

meta constant pow : float → float → float
meta instance has_float_pow : has_pow float float := ⟨pow⟩

/-- Square root. -/
meta constant sqrt : float → float
/-- Cube root. -/
meta constant cbrt : float → float

/-- Computes `sqrt(x^2 + y^2)`. -/
meta constant hypot : float → float → float

/-- Exponential function. -/
meta constant exp : float → float
/-- 2 raised to the given power. -/
meta constant exp2 : float → float
/-- Natural logarithm. -/
meta constant log : float → float
meta constant log2 : float → float
meta constant log10 : float → float

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
meta constant asinh : float → float
meta constant acosh : float → float
meta constant atanh : float → float

meta constant abs : float → float
/-- Nearest integer not less than the given value. Input must be finite. -/
meta constant ceil : float → int
/-- Nearest integer not greater than the given value. Input must be finite. -/
meta constant floor : float → int
/-- Nearest integer not greater in magnitude than the given value. Input must be finite. -/
meta constant trunc : float → int
/-- Round to the nearest integer, rounding away from zero in halfway cases. Input must be finite. -/
meta constant round : float → int

meta constant lt : float → float → bool
meta instance : has_lt float := ⟨λ x y, lt x y⟩
meta instance decidable_lt : decidable_rel (float.has_lt.lt) := by apply_instance
meta constant le : float → float → bool
meta instance : has_le float := ⟨λ x y, le x y⟩
meta instance decidable_le : decidable_rel (float.has_le.le) := by apply_instance
meta constant dec_eq : decidable_eq float
attribute [instance] dec_eq

meta constant of_nat : nat → float
meta constant of_int : int → float
meta instance of_nat_coe : has_coe nat float := ⟨of_nat⟩
meta instance of_int_coe : has_coe int float := ⟨of_int⟩
protected meta def zero : float := of_nat 0
protected meta def one : float := of_nat 1
meta instance : has_zero float := ⟨float.zero⟩
meta instance : has_one float := ⟨float.one⟩

meta constant to_repr : float → string
meta instance : has_repr float := ⟨to_repr⟩
meta instance : has_to_string float := ⟨to_repr⟩
meta instance : has_to_format float := ⟨format.of_string ∘ to_string⟩

meta constant of_string : string → option float

meta instance has_nat_pow : has_pow float nat :=
⟨λ a b, native.float.pow a (float.of_nat b)⟩

end float
end native
