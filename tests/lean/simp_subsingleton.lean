inductive some_subsingleton : Type | canonical
open some_subsingleton
instance : subsingleton some_subsingleton := ⟨λ a b, by cases a; cases b; refl⟩
-- Note that ⟨λ a b, refl a⟩ does not work as a valid instance:
-- the type is a subsingleton, but not definitionally!

def some_function : some_subsingleton → some_subsingleton := λ x, x

@[simp] lemma some_function_lemma {a : some_subsingleton} :
  some_function a = canonical := by cases a; refl

-- Motivating example:
example (a : some_subsingleton) : some_function a = canonical := by simp only [some_function_lemma]

example (a : some_subsingleton) : some_function a = canonical :=
by {(do
  t <- tactic.target,
  c <- tactic.mk_specialized_congr_lemma_simp t,
  tactic.trace c.arg_kinds), simp }

example : cond (to_bool (2 = 2)) 0 1 = 0 :=
by {(do
  `((cond %%t %%i %%e) = _) <- tactic.target,
  c <- tactic.mk_specialized_congr_lemma_simp t,
  tactic.trace c.arg_kinds), simp }

constants (γ : Type) (f : Π (α : Type*) (β : Sort*), α → β → γ)
          (X : Type) (X_ss : subsingleton X)
          (Y : Prop)

attribute [instance] X_ss

example (x₁ x₂ : X) (y₁ y₂ : Y) : f X Y x₁ y₁ = f X Y x₂ y₂ :=
by { (do
  `(%%t = _) <- tactic.target,
  cs <- tactic.mk_specialized_congr_lemma_simp t,
  tactic.trace cs.arg_kinds), congr }
