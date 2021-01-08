set_option pp.notation false
set_option pp.implicit true
set_option pp.numerals false
set_option pp.binder_types true

variables (A : Type*) [has_add A] [has_one A] [has_lt A] (a : A)

#check a + 1

#check λ (H : a > 1), a + 1

#check λ (H₁ : a > 1) (H₂ : a < 5), a + 1
