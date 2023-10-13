set_option pp.parens true

#check 1 + 2 * 3 + 4

#check @nat.add_assoc

#check [1,2,3]++[3,4,5]

#check ∀ (x y z : ℤ), x - (-3) = -2 + x
#check Π (x y : ℤ), {x : ℤ // x - (-3) = -2 + x}
#check ∀ (p : ℕ → ℕ → Prop), p (1 + 2) 3
#check ∀ (f : ℕ → ℕ → ℕ), f 2 (f 3 4 + 1) + 2 = f 1 2

def Union {ι β : Type*} (s : ι → set β) : set β := {x : β | ∃ i, x ∈ s i}
notation `⋃` binders `, ` r:(scoped f, Union f) := r

#check (set.univ : set ℕ) = ⋃(n:ℕ), {m : ℕ | m < n}

-- subtype notation is handled specially by the pretty printer, so isn't parenthesized
#check {x : ℕ // x ∈ set.univ}
