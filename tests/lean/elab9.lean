set_option pp.notation false
set_option pp.implicit true
set_option pp.numerals false
set_option pp.binder_types true

#check
begin
    tactic.unfreeze_local_instances,
    exact λ (A : Type*) [has_add A] [has_zero A] (a : A) (H : a + 0 = a) [has_add A] (H : a = 0 + 0), a + a
end

#check
begin
    tactic.unfreeze_local_instances,
    exact λ (a b : nat) (H : a > b) [has_lt nat], a < b
end
