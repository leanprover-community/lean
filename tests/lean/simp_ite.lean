-- in older versions, this would get stuck on the equality
-- `decidable_of_decidable_of_iff dec_p p_iff_p' = dec_p'`
constants (p p' : Prop) (p_iff_p' : p ↔ p')
attribute [simp] p_iff_p'
example (a b : ℕ) [dec_p : decidable p] [dec_p' : decidable p'] :
  (if p then a else b) = (if p' then a else b) :=
by simp

-- `simp` shouldn't try rewrite `p` to `p'` without the instance, but still rewrite `a` to `a'`
constants (a a' b : ℕ) (a_eq_a' : a = a')
attribute [simp] a_eq_a'
example [decidable p] : (if p then a else b) = (if p then a' else b) := by simp
