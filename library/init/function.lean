/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Haitao Zhang
-/
prelude
import init.data.prod init.funext init.logic
/-!
# General operations on functions
-/
universes u₁ u₂ u₃ u₄

namespace function
variables {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {δ : Sort u₄} {ζ : Sort u₁}

/-- Composition of functions: `(f ∘ g) x = f (g x)`. -/
@[inline, reducible] def comp (f : β → φ) (g : α → β) : α → φ :=
λ x, f (g x)

/-- Composition of dependent functions: `(f ∘' g) x = f (g x)`, where type of `g x` depends on `x`
and type of `f (g x)` depends on `x` and `g x`. -/
@[inline, reducible] def dcomp {β : α → Sort u₂} {φ : Π {x : α}, β x → Sort u₃}
  (f : Π {x : α} (y : β x), φ y) (g : Π x, β x) : Π x, φ (g x) :=
λ x, f (g x)

infixr ` ∘ `:90  := function.comp
infixr ` ∘' `:80 := function.dcomp

@[reducible] def comp_right (f : β → β → β) (g : α → β) : β → α → β :=
λ b a, f b (g a)

@[reducible] def comp_left (f : β → β → β) (g : α → β) : α → β → β :=
λ a b, f (g a) b

/-- Given functions `f : β → β → φ` and `g : α → β`, produce a function `α → α → φ` that evaluates
`g` on each argument, then applies `f` to the results. Can be used, e.g., to transfer a relation
from `β` to `α`. -/
@[reducible] def on_fun (f : β → β → φ) (g : α → β) : α → α → φ :=
λ x y, f (g x) (g y)

@[reducible] def combine (f : α → β → φ) (op : φ → δ → ζ) (g : α → β → δ)
  : α → β → ζ :=
λ x y, op (f x y) (g x y)

/-- Constant `λ _, a`. -/
@[reducible] def const (β : Sort u₂) (a : α) : β → α :=
λ x, a

@[reducible] def swap {φ : α → β → Sort u₃} (f : Π x y, φ x y) : Π y x, φ x y :=
λ y x, f x y

@[reducible] def app {β : α → Sort u₂} (f : Π x, β x) (x : α) : β x :=
f x

infixl  ` on `:2         := on_fun
notation f ` -[` op `]- ` g  := combine f op g

lemma left_id (f : α → β) : id ∘ f = f := rfl

lemma right_id (f : α → β) : f ∘ id = f := rfl

@[simp] lemma comp_app (f : β → φ) (g : α → β) (a : α) : (f ∘ g) a = f (g a) := rfl

lemma comp.assoc (f : φ → δ) (g : β → φ) (h : α → β) : (f ∘ g) ∘ h = f ∘ (g ∘ h) := rfl

@[simp] lemma comp.left_id (f : α → β) : id ∘ f = f := rfl

@[simp] lemma comp.right_id (f : α → β) : f ∘ id = f := rfl

lemma comp_const_right (f : β → φ) (b : β) : f ∘ (const α b) = const α (f b) := rfl

/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
def injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

lemma injective.comp {g : β → φ} {f : α → β} (hg : injective g) (hf : injective f) :
  injective (g ∘ f) :=
assume a₁ a₂, assume h, hf (hg h)

/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
@[reducible] def surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b

lemma surjective.comp {g : β → φ} {f : α → β} (hg : surjective g) (hf : surjective f) :
  surjective (g ∘ f) :=
λ (c : φ), exists.elim (hg c) (λ b hb, exists.elim (hf b) (λ a ha,
  exists.intro a (show g (f a) = c, from (eq.trans (congr_arg g ha) hb))))

/-- A function is called bijective if it is both injective and surjective. -/
def bijective (f : α → β) := injective f ∧ surjective f

lemma bijective.comp {g : β → φ} {f : α → β} : bijective g → bijective f → bijective (g ∘ f)
| ⟨h_ginj, h_gsurj⟩ ⟨h_finj, h_fsurj⟩ := ⟨h_ginj.comp h_finj, h_gsurj.comp h_fsurj⟩

/-- `left_inverse g f` means that g is a left inverse to f. That is, `g ∘ f = id`. -/
def left_inverse (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x

/-- `has_left_inverse f` means that `f` has an unspecified left inverse. -/
def has_left_inverse (f : α → β) : Prop := ∃ finv : β → α, left_inverse finv f

/-- `right_inverse g f` means that g is a right inverse to f. That is, `f ∘ g = id`. -/
def right_inverse (g : β → α) (f : α → β) : Prop := left_inverse f g

/-- `has_right_inverse f` means that `f` has an unspecified right inverse. -/
def has_right_inverse (f : α → β) : Prop := ∃ finv : β → α, right_inverse finv f

lemma left_inverse.injective {g : β → α} {f : α → β} : left_inverse g f → injective f :=
assume h a b faeqfb,
calc a = g (f a) : (h a).symm
... = g (f b) : congr_arg g faeqfb
... = b : h b

lemma has_left_inverse.injective {f : α → β} : has_left_inverse f → injective f :=
assume h, exists.elim h (λ finv inv, inv.injective)

lemma right_inverse_of_injective_of_left_inverse {f : α → β} {g : β → α}
    (injf : injective f) (lfg : left_inverse f g) :
  right_inverse f g :=
assume x,
have h : f (g (f x)) = f x, from lfg (f x),
injf h

lemma right_inverse.surjective {f : α → β} {g : β → α} (h : right_inverse g f) : surjective f :=
assume y, ⟨g y, h y⟩

lemma has_right_inverse.surjective {f : α → β} : has_right_inverse f → surjective f
| ⟨finv, inv⟩ := inv.surjective

lemma left_inverse_of_surjective_of_right_inverse {f : α → β} {g : β → α}
    (surjf : surjective f) (rfg : right_inverse f g) :
  left_inverse f g :=
assume y, exists.elim (surjf y) (λ x hx, calc
  f (g y) = f (g (f x)) : hx ▸ rfl
      ... = f x         : eq.symm (rfg x) ▸ rfl
      ... = y           : hx)

lemma injective_id : injective (@id α) := assume a₁ a₂ h, h

lemma surjective_id : surjective (@id α) := assume a, ⟨a, rfl⟩

lemma bijective_id : bijective (@id α) := ⟨injective_id, surjective_id⟩

end function

namespace function
variables {α : Type u₁} {β : Type u₂} {φ : Type u₃}

/-- Interpret a function on `α × β` as a function with two arguments. -/
@[inline] def curry : (α × β → φ) → α → β → φ :=
λ f a b, f (a, b)

/-- Interpret a function with two arguments as a function on `α × β` -/
@[inline] def uncurry : (α → β → φ) → α × β → φ :=
λ f a, f a.1 a.2

@[simp] lemma curry_uncurry (f : α → β → φ) : curry (uncurry f) = f :=
rfl

@[simp] lemma uncurry_curry (f : α × β → φ) : uncurry (curry f) = f :=
funext (λ ⟨a, b⟩, rfl)

protected lemma left_inverse.id {g : β → α} {f : α → β} (h : left_inverse g f) : g ∘ f = id :=
funext h

protected lemma right_inverse.id {g : β → α} {f : α → β} (h : right_inverse g f) : f ∘ g = id :=
funext h

end function
