open quot
variables {A : Type} {B : A → Type}

variable f : Π a : A, B a

local attribute [instance] function.fun_setoid

#reduce λ x, quot.lift_on ⟦f⟧ (λf : (Πx : A, B x), f) _ x

example (x : A) : quot.lift_on ⟦f⟧ (λf : (Πx : A, B x), f) sorry x = f x :=
rfl
