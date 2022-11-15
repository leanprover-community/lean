open tactic

structure point (α : Type*) :=
(x : α) (y : α)

example : ∀ i : ℤ, (i, i).snd = i + 0 + (point.mk 0 i).x := by do
os ← get_options,
set_options (os.set_bool `pp.links tt)

example : ∃ i j : ℤ, true := by do
os ← get_options,
set_options (os.set_bool `pp.links tt)
