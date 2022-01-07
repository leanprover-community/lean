def c : ℕ := default
def d : ℕ := default

local attribute [simp] nat.add_zero

class foo (α : Type)
-- type class resolution for [foo α] will always time out
instance foo.foo {α} [foo α] : foo α := ‹foo α›

-- would break simp on any term containing c
@[simp] lemma c_eq_d [foo ℕ] : c = d := by refl

set_option trace.simplify.rewrite true
example : c = d + 0 :=
begin
  -- shouldn't fail, even though type class resolution for c_eq_d times out
  simp,
  guard_target c = d,
  refl,
end
