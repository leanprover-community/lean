class test_neg_neg (R : Type) extends has_neg R, has_one R :=
(neg_neg : ∀ r : R, -(-r) = r)

variable R : Type
variable [test_neg_neg R]

example : -(-(1:R)) = 1 :=
begin
  trace_state,
  exact test_neg_neg.neg_neg 1,
end

#check - -(1:R)
