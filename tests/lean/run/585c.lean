namespace list

inductive perm {α} : list α → list α → Prop
| nil   : perm [] []
| cons  : Π (x : α) {l₁ l₂ : list α}, perm l₁ l₂ → perm (x::l₁) (x::l₂)
| swap  : Π (x y : α) (l : list α), perm (y::x::l) (x::y::l)
| trans : Π {l₁ l₂ l₃ : list α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

infix ~ := perm

@[refl] protected axiom perm.refl {α} : ∀ (l : list α), l ~ l

@[symm] protected axiom perm.symm {α} {l₁ l₂ : list α} (p : l₁ ~ l₂) : l₂ ~ l₁

attribute [trans] perm.trans

end list

example (α) (l : list α) (a b : α) :
  a :: b :: l ~ b :: a :: l :=
begin
  success_if_fail { simp [← list.perm.cons] }, -- 💣
  apply list.perm.swap
end

