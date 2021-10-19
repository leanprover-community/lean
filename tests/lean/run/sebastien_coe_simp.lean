variable (α : Type*)

structure my_equiv :=
(to_fun : α → α)

instance : has_coe_to_fun (my_equiv α) _ := ⟨my_equiv.to_fun⟩

def my_equiv1 : my_equiv α :=
{ to_fun := id }

def my_equiv2 : my_equiv α :=
{ to_fun := id }

@[simp] lemma one_eq_two : my_equiv1 α = my_equiv2 α := rfl

lemma other (x : ℕ) : my_equiv1 ℕ (x + 0) = my_equiv2 ℕ x := by simp [nat.add_zero] -- does not fail

@[simp] lemma two_apply (x : α) : my_equiv2 α x = x := rfl

lemma one_apply (x : α) : my_equiv1 α x = x := by simp -- does not fail
