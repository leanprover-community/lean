class A (α : Type)
class B (α : Type) [A α]

def P (α : Type) : Prop := true

@[simp] lemma foo (α : Type) [A α] [B α] : P α ↔ true := iff.rfl

-- should work
example (α : Type) [A α] [B α] : P α ↔ id true :=
begin
  simp only [foo],
  guard_target true ↔ id true,
  refl
end