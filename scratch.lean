
def asdf {P Q : Prop} : P → Q → P ∧ Q :=
begin
  intro p,
  intro q,
  split,
  assumption,
  assumption
end