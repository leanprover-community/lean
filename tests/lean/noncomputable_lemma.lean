noncomputable lemma a : ℕ := 37
lemma b : ℕ := 37
-- do not report missing noncomputable:
lemma sorry_type : sorry := sorry
-- do not report missing noncomputable:
lemma incomplete :
