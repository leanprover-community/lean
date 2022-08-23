open nat

inductive Expr
| zero : Expr
| one  : Expr
| add  : Expr → Expr → Expr

namespace Expr

inductive direct_subterm : Expr → Expr → Prop
| add_1 : ∀ e₁ e₂ : Expr, direct_subterm e₁ (add e₁ e₂)
| add_2 : ∀ e₁ e₂ : Expr, direct_subterm e₂ (add e₁ e₂)

theorem direct_subterm_wf : well_founded direct_subterm :=
begin
  constructor, intro e, induction e,
  repeat { constructor, intros y hlt, cases hlt; assumption },
end

inductive tc {α : Sort*} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c

-- The transitive closure of a well-founded relation is well-founded
-- (moved to mathlib)
namespace tc
section
  parameters {α : Sort*} {r : α → α → Prop}
  local notation `r⁺` := tc r

  lemma accessible {z : α} (ac : acc r z) : acc (tc r) z :=
  acc.rec_on ac (λ x acx ih,
    acc.intro x (λ y rel,
      tc.rec_on rel
        (λ a b rab acx ih, ih a rab)
        (λ a b c rab rbc ih₁ ih₂ acx ih, acc.inv (ih₂ acx ih) rab)
        acx ih))

  lemma wf (h : well_founded r) : well_founded r⁺ :=
  ⟨λ a, accessible (h.apply a)⟩
end
end tc

definition subterm := tc direct_subterm

theorem subterm_wf : well_founded subterm :=
tc.wf direct_subterm_wf

local infix (name := add) `+` := Expr.add

set_option pp.notation false

definition ev : Expr → nat
| zero             := 0
| one              := 1
| ((a : Expr) + b) := has_add.add (ev a) (ev b)

definition foo : Expr := add zero (add one one)

example : ev foo = 2 :=
rfl
end Expr
