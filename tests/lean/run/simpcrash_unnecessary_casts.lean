class ss : Type
instance : subsingleton ss := ⟨λ ⟨⟩ ⟨⟩, rfl⟩
instance : decidable_eq ss := λ ⟨⟩ ⟨⟩, decidable.is_true rfl
instance ss.inst : ss := ⟨⟩

def vector (n : nat) (α : Type) := fin n → α

def vector.get {n α} [ss] (v : vector n α) (i : nat) (h : i < n) : α :=
v ⟨i, h⟩

example (v : vector 7 nat) :
  @vector.get _ nat (eq.rec (λ _ : unit, ss.inst) (eq.refl 42) ()) v 3 dec_trivial > 42 :=
begin
  simp only [show 3 = 1 + 1 + 1, from rfl],
  sorry,
end
