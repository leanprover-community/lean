-- Options (particularly trace options) are refreshed
-- upon entry to the simplifier.

example {p : Prop} (h : p) : p :=
begin
  have h₁ : true = true := rfl,
  have h₂ : true = true := rfl,
  have h₃ : true = true := rfl,
  simp at h₁,
  tactic.set_bool_option `trace.simplify.rewrite tt,
  simp at h₂,
  tactic.set_bool_option `pp.all tt,
  simp at h₃,
  exact h
end
