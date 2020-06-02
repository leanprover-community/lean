variables {α : Type} [has_neg α]
variables [has_add α] [has_sub α] [has_mul α] [has_div α] [has_pow α α]
variables (x y : α)

example : - x + y = (- x) + y := rfl
example : - x - y = (- x) - y := rfl
-- `- (x * y)` and `- (x / y)` would also be fine,
-- but breaks an annoyingly-large number of things in mathlib.
example : - x * y = (- x) * y := rfl
example : - x / y = (- x) / y := rfl
example : - x ^ y = - (x ^ y) := rfl
