structure hom (α β : Type*) := (f : α → β)

instance {α β} : has_coe_to_fun (hom α β) := ⟨_, hom.f⟩

def frob {α β} (a : α) : hom β (α × β) := ⟨λ b, (a, b)⟩

-- `(frob 1 : hom ?m_1 (?m_2 × ?m_1))` has metavariables in the type
def foo : ℤ × ℤ := frob 1 2

example : foo = (1, 2) := rfl
