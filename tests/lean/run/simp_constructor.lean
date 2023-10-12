inductive term
| var : string → term
| app : string → list term → term

example (h : term.var "a" = term.app "f" []) : false :=
begin
  simp at h,
  exact false.elim h
end

example : ¬ term.var "a" = term.app "f" [] :=
by simp

universes u

inductive vec (α : Type u) : nat → Type u
| nil  : vec 0
| cons : Π {n}, α → vec n → vec (nat.succ n)

#check @vec.cons.inj_eq

def wrapped_nat (n : nat) := nat

structure with_wrapped : Type :=
(n : nat)
(m : wrapped_nat n)

-- #812: this should use `==` not `=` as `m` and `m'` are not reducibly defeq
#check (@with_wrapped.mk.inj_eq :
  ∀ {n : ℕ} {m : wrapped_nat n} {n' : ℕ} {m' : wrapped_nat n'},
    with_wrapped.mk n m = with_wrapped.mk n' m' = (n = n' ∧ m == m'))

example (a b : nat) (h : a == b) : a + 1 = b + 1 :=
begin
  subst h
end

mutual inductive Expr, Expr_list
with Expr : Type
| var : string → Expr
| app : string → Expr_list → Expr
with Expr_list : Type
| nil  : Expr_list
| cons : Expr → Expr_list → Expr_list

#check @Expr.app.inj_eq

example {α : Type u} (n : nat) (a₁ a₂ : α) (t : vec α n) (h : vec.cons a₁ t = vec.cons a₂ t) : a₁ = a₂ :=
begin
  simp at h,
  exact h
end

example (a₁ a₂ : nat) (h₁ : a₁ > 0) (h₂ : a₂ > 0) (h : a₁ = a₂) : subtype.mk a₁ h₁ = subtype.mk a₂ h₂ :=
begin
  simp,
  exact h
end

example (a₁ a₂ : nat) (h₁ : a₁ > 0) (h₂ : a₂ > 0) (h : subtype.mk a₁ h₁ = subtype.mk a₂ h₂) : a₁ = a₂ :=
begin
  simp at h,
  exact h
end
