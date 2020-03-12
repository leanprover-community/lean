constants (p : (nat → nat → nat) → Prop) (p_add : p nat.add)

-- The failure case we want to avoid is unfolding `nat.add` and not `λ a b, nat.add a b`
example : p (λ a b, nat.add a b) := p_add
