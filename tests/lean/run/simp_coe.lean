example (p : Prop) (h : p) : tt → p :=
begin
  simp [true_implies_iff], assumption
end

local attribute [semireducible] coe_sort_bool

example (p : Prop) (h : p) : tt → p :=
begin
  fail_if_success {simp},
  intro, assumption
end

local attribute [reducible] coe_sort_bool

example (p : Prop) (h : p) : tt → p :=
begin
  simp [true_implies_iff], assumption
end
