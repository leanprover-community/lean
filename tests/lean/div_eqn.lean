def Div : nat → nat → nat
| x y :=
  if h : 0 < y ∧ y ≤ x then
    have @has_well_founded.r _
      (@psigma.has_well_founded _ _ _ (λ _, has_well_founded_of_has_sizeof ℕ))
      (psigma.mk (x - y) y) (psigma.mk x y) :=
    begin
      apply psigma.lex.left,
      exact nat.sub_lt (nat.lt_of_lt_of_le h.left h.right) h.left,
    end,
    Div (x - y) y + 1
  else
    0

#check Div.equations._eqn_1
