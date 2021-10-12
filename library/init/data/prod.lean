/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
prelude
import init.logic
universes u v

section
variables {α : Type u} {β : Type v}

@[simp] lemma prod.mk.eta : ∀{p : α × β}, (p.1, p.2) = p
| (a, b) := rfl

instance [inhabited α] [inhabited β] : inhabited (prod α β) :=
⟨(default α, default β)⟩

instance [h₁ : decidable_eq α] [h₂ : decidable_eq β] : decidable_eq (α × β)
| (a, b) (a', b') :=
  match (h₁ a a') with
  | (is_true e₁) :=
    match (h₂ b b') with
    | (is_true e₂)  := is_true (eq.rec_on e₁ (eq.rec_on e₂ rfl))
    | (is_false n₂) := is_false (assume h, prod.no_confusion h (λ e₁' e₂', absurd e₂' n₂))
    end
  | (is_false n₁) := is_false (assume h, prod.no_confusion h (λ e₁' e₂', absurd e₁' n₁))
  end

end

def {u₁ u₂ v₁ v₂} prod.map {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂}
  (f : α₁ → α₂) (g : β₁ → β₂) (x : α₁ × β₁) : α₂ × β₂ :=
(f x.1, g x.2)
