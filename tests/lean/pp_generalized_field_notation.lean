set_option pp.generalized_field_notation true

#check int.nat_abs_zero
#check int.sign_zero
#check int.sign_mul_nat_abs

lemma list.reverse_reverse {α} (xs : list α) : xs.reverse.reverse = xs :=
sorry

#check list.reverse_reverse

def prod.swap {α β} : α × β → β × α | ⟨a, b⟩ := ⟨b, a⟩

lemma prod.swap_swap {α β} (p : α × β) : p.swap.swap = p :=
by cases p; refl

#check prod.swap_swap