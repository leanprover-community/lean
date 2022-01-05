namespace in_param

class A (α β : Type) -- no out_param!
instance inst : A ℕ ℤ := ⟨⟩
def p (_ : Type) : Prop := false
@[simp] lemma l {α β} [A α β] : p α ↔ p β := iff.rfl

-- `simp` should fail to apply `l` here since the `β` parameter to `l` can't be inferred,
-- instead of trying to synthesize an instance `A ℕ ?m_1`, find `inst` and unify `?m_1 =?= ℤ`,
-- turning the goal into `p ℤ`
example : p ℕ := by simp

end in_param

namespace out_param

-- However, if `β` is marked as an out_param, the goal should turn into `p ℤ`
class A (α : Type) (β : out_param Type) -- no out_param!
instance inst : A ℕ ℤ := ⟨⟩
def p (_ : Type) : Prop := false
@[simp] lemma l {α β} [A α β] : p α ↔ p β := iff.rfl
example : p ℕ := by simp

end out_param
