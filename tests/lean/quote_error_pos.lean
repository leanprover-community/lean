open tactic

class add_monoid (α : Type) extends has_zero α, has_add α :=
(zero_add : ∀ a : α, 0 + a = a)

lemma zero_add {α : Type} [add_monoid α] (a : α) : (0 : α) + a = a :=
add_monoid.zero_add a

meta def apply_zero_add (a : pexpr) : tactic unit :=
to_expr ``(zero_add %%a) >>= exact

example (a : nat) : 0 + a = a :=
begin
  apply_zero_add ``(tt), -- Error should be here
end

meta def apply_zero_add2 (a : pexpr) : tactic unit :=
`[apply zero_add %%a]

example (a : nat) : 0 + a = a :=
begin
  apply_zero_add2 ``(tt), -- Error should be here
end
