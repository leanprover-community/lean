def psum.alt'.sizeof {α β} [has_sizeof α] [has_sizeof β] : psum α β → nat
| (psum.inl a) := 2*sizeof a + 2
| (psum.inr b) := 2*sizeof b + 1

def sum_has_sizeof_2 {α β} [has_sizeof α] [has_sizeof β] : has_sizeof (psum α β) :=
⟨psum.alt'.sizeof⟩

local attribute [instance] sum_has_sizeof_2
local attribute [simp] nat.add_comm nat.add_left_comm nat.add_assoc nat.mul_assoc nat.mul_comm nat.one_mul

mutual def f, g
with f : ℕ → ℕ
| n :=
  have has_well_founded.r (psum.inr n) (psum.inl n), from nat.lt_succ_self _,
  g n + 1
with g : ℕ → ℕ
| 0     := 0
| (n+1) :=
  /- The following is a hint for the equation compiler.
     We will be able to delete it as soon as we have decision procedures for arithmetic -/
  have has_well_founded.r (psum.inl n) (psum.inr (n + 1)), from
    begin
      unfold has_well_founded.r sizeof_measure measure inv_image,
      unfold sizeof has_sizeof.sizeof psum.alt'.sizeof nat.sizeof,
      rw [nat.left_distrib], simp,
      rw [nat.add_comm 1 _],
      exact nat.lt_succ_self _,
    end,
  f n
