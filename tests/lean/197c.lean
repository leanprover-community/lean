structure S1 :=
(carrier : set ℕ)
(a1 : ∀ x ∈ carrier, true)

structure S2 extends S1 :=
(a2 : ∀ x ∈ carrier, true)

def example_1 : S2 :=
{ carrier := ∅,
  a1 := by { intros x hx, trivial },
  -- The goal for `a2` becomes:
  -- ⊢ ∀ (x : G), set.mem x ∅ → true
  -- Note in particular that `∈` has been unfolded inappropriately to `set.mem`.
  a2 := by { trace_state, sorry } }

-- One workaround is to introduce the variables in `a1'`
-- before the tactic block.
def example_2 : S2 :=
{ carrier := ∅,
  a1 := λ x hx, trivial,
  -- Now the goal contains a `{ carrier := ... }.carrier`,
  -- but even when we `dsimp` this, the `∈` is not disturbed.
  a2 := by { dsimp, trace_state, sorry } }


set_option old_structure_cmd true
class semigroup (α : Type*) extends has_mul α :=
(mul_assoc : ∀ x y z : α, x * y * z = x * (y * z))

set_option pp.all true
#print semigroup

example : semigroup ℕ :=
{ mul := (*),
  mul_assoc := _ }