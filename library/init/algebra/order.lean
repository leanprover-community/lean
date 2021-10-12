/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.logic init.classical init.meta.name init.algebra.classes
/- Make sure instances defined in this file have lower priority than the ones
   defined for concrete structures -/
set_option default_priority 100

set_option old_structure_cmd true

universe u
variables {α : Type u}

set_option auto_param.check_exists false

section preorder

/-!
### Definition of `preorder` and lemmas about types with a `preorder`
-/

/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class preorder (α : Type u) extends has_le α, has_lt α :=
(le_refl : ∀ a : α, a ≤ a)
(le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
(lt := λ a b, a ≤ b ∧ ¬ b ≤ a)
(lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) . order_laws_tac)

variables [preorder α]

/-- The relation `≤` on a preorder is reflexive. -/
@[refl] lemma le_refl : ∀ a : α, a ≤ a :=
preorder.le_refl

/-- The relation `≤` on a preorder is transitive. -/
@[trans] lemma le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c :=
preorder.le_trans

lemma lt_iff_le_not_le : ∀ {a b : α}, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) :=
preorder.lt_iff_le_not_le

lemma lt_of_le_not_le : ∀ {a b : α}, a ≤ b → ¬ b ≤ a → a < b
| a b hab hba := lt_iff_le_not_le.mpr ⟨hab, hba⟩

lemma le_not_le_of_lt : ∀ {a b : α}, a < b → a ≤ b ∧ ¬ b ≤ a
| a b hab := lt_iff_le_not_le.mp hab

lemma le_of_eq {a b : α} : a = b → a ≤ b :=
λ h, h ▸ le_refl a

@[trans] lemma ge_trans : ∀ {a b c : α}, a ≥ b → b ≥ c → a ≥ c :=
λ a b c h₁ h₂, le_trans h₂ h₁

lemma lt_irrefl : ∀ a : α, ¬ a < a
| a haa := match le_not_le_of_lt haa with
  | ⟨h1, h2⟩ := false.rec _ (h2 h1)
  end

lemma gt_irrefl : ∀ a : α, ¬ a > a :=
lt_irrefl

@[trans] lemma lt_trans : ∀ {a b c : α}, a < b → b < c → a < c
| a b c hab hbc :=
  match le_not_le_of_lt hab, le_not_le_of_lt hbc with
  | ⟨hab, hba⟩, ⟨hbc, hcb⟩ := lt_of_le_not_le (le_trans hab hbc) (λ hca, hcb (le_trans hca hab))
  end

@[trans] lemma gt_trans : ∀ {a b c : α}, a > b → b > c → a > c :=
λ a b c h₁ h₂, lt_trans h₂ h₁

lemma ne_of_lt {a b : α} (h : a < b) : a ≠ b :=
λ he, absurd h (he ▸ lt_irrefl a)

lemma ne_of_gt {a b : α} (h : b < a) : a ≠ b :=
λ he, absurd h (he ▸ lt_irrefl a)

lemma lt_asymm {a b : α} (h : a < b) : ¬ b < a :=
λ h1 : b < a, lt_irrefl a (lt_trans h h1)

lemma le_of_lt : ∀ {a b : α}, a < b → a ≤ b
| a b hab := (le_not_le_of_lt hab).left

@[trans] lemma lt_of_lt_of_le : ∀ {a b c : α}, a < b → b ≤ c → a < c
| a b c hab hbc :=
  let ⟨hab, hba⟩ := le_not_le_of_lt hab in
  lt_of_le_not_le (le_trans hab hbc) $ λ hca, hba (le_trans hbc hca)

@[trans] lemma lt_of_le_of_lt : ∀ {a b c : α}, a ≤ b → b < c → a < c
| a b c hab hbc :=
  let ⟨hbc, hcb⟩ := le_not_le_of_lt hbc in
  lt_of_le_not_le (le_trans hab hbc) $ λ hca, hcb (le_trans hca hab)

@[trans] lemma gt_of_gt_of_ge {a b c : α} (h₁ : a > b) (h₂ : b ≥ c) : a > c :=
lt_of_le_of_lt h₂ h₁

@[trans] lemma gt_of_ge_of_gt {a b c : α} (h₁ : a ≥ b) (h₂ : b > c) : a > c :=
lt_of_lt_of_le h₂ h₁

lemma not_le_of_gt {a b : α} (h : a > b) : ¬ a ≤ b :=
(le_not_le_of_lt h).right

lemma not_lt_of_ge {a b : α} (h : a ≥ b) : ¬ a < b :=
λ hab, not_le_of_gt hab h

lemma le_of_lt_or_eq : ∀ {a b : α}, (a < b ∨ a = b) → a ≤ b
| a b (or.inl hab) := le_of_lt hab
| a b (or.inr hab) := hab ▸ le_refl _

lemma le_of_eq_or_lt {a b : α} (h : a = b ∨ a < b) : a ≤ b :=
or.elim h le_of_eq le_of_lt

instance decidable_lt_of_decidable_le [decidable_rel ((≤) : α → α → Prop)] :
  decidable_rel ((<) : α → α → Prop)
| a b :=
  if hab : a ≤ b then
    if hba : b ≤ a then
      is_false $ λ hab', not_le_of_gt hab' hba
    else
      is_true $ lt_of_le_not_le hab hba
  else
    is_false $ λ hab', hab (le_of_lt hab')

end preorder

section partial_order

/-!
### Definition of `partial_order` and lemmas about types with a partial order
-/

/-- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
class partial_order (α : Type u) extends preorder α :=
(le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)

variables [partial_order α]

lemma le_antisymm : ∀ {a b : α}, a ≤ b → b ≤ a → a = b :=
partial_order.le_antisymm

lemma le_antisymm_iff {a b : α} : a = b ↔ a ≤ b ∧ b ≤ a :=
⟨λe, ⟨le_of_eq e, le_of_eq e.symm⟩, λ⟨h1, h2⟩, le_antisymm h1 h2⟩

lemma lt_of_le_of_ne {a b : α} : a ≤ b → a ≠ b → a < b :=
λ h₁ h₂, lt_of_le_not_le h₁ $ mt (le_antisymm h₁) h₂

instance decidable_eq_of_decidable_le [decidable_rel ((≤) : α → α → Prop)] :
  decidable_eq α
| a b :=
  if hab : a ≤ b then
    if hba : b ≤ a then
      is_true (le_antisymm hab hba)
    else
      is_false (λ heq, hba (heq ▸ le_refl _))
  else
    is_false (λ heq, hab (heq ▸ le_refl _))

namespace decidable

variables [@decidable_rel α (≤)]

lemma lt_or_eq_of_le {a b : α} (hab : a ≤ b) : a < b ∨ a = b :=
if hba : b ≤ a then or.inr (le_antisymm hab hba)
else or.inl (lt_of_le_not_le hab hba)

lemma eq_or_lt_of_le {a b : α} (hab : a ≤ b) : a = b ∨ a < b :=
(lt_or_eq_of_le hab).swap

lemma le_iff_lt_or_eq {a b : α} : a ≤ b ↔ a < b ∨ a = b :=
⟨lt_or_eq_of_le, le_of_lt_or_eq⟩

end decidable

local attribute [instance] classical.prop_decidable

lemma lt_or_eq_of_le {a b : α} : a ≤ b → a < b ∨ a = b := decidable.lt_or_eq_of_le

lemma le_iff_lt_or_eq {a b : α} : a ≤ b ↔ a < b ∨ a = b := decidable.le_iff_lt_or_eq

end partial_order

section linear_order

/-!
### Definition of `linear_order` and lemmas about types with a linear order
-/

/-- Default definition of `max`. -/
def max_default {α : Type u} [has_le α] [decidable_rel ((≤) : α → α → Prop)] (a b : α) :=
if b ≤ a then a else b

/-- Default definition of `min`. -/
def min_default {α : Type u} [has_le α] [decidable_rel ((≤) : α → α → Prop)] (a b : α) :=
if a ≤ b then a else b

/-- A linear order is reflexive, transitive, antisymmetric and total relation `≤`.
We assume that every linear ordered type has decidable `(≤)`, `(<)`, and `(=)`. -/
class linear_order (α : Type u) extends partial_order α :=
(le_total : ∀ a b : α, a ≤ b ∨ b ≤ a)
(decidable_le : decidable_rel (≤))
(decidable_eq : decidable_eq α := @decidable_eq_of_decidable_le _ _ decidable_le)
(decidable_lt : decidable_rel ((<) : α → α → Prop) :=
    @decidable_lt_of_decidable_le _ _ decidable_le)
(max : α → α → α := @max_default α _ _)
(max_def : max = @max_default α _ decidable_le . tactic.interactive.reflexivity)
(min : α → α → α := @min_default α _ _)
(min_def : min = @min_default α _ decidable_le . tactic.interactive.reflexivity)

variables [linear_order α]

local attribute [instance] linear_order.decidable_le

lemma le_total : ∀ a b : α, a ≤ b ∨ b ≤ a :=
linear_order.le_total

lemma le_of_not_ge {a b : α} : ¬ a ≥ b → a ≤ b :=
or.resolve_left (le_total b a)

lemma le_of_not_le {a b : α} : ¬ a ≤ b → b ≤ a :=
or.resolve_left (le_total a b)

lemma not_lt_of_gt {a b : α} (h : a > b) : ¬ a < b :=
lt_asymm h

lemma lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a :=
or.elim (le_total a b)
  (λ h : a ≤ b, or.elim (decidable.lt_or_eq_of_le h)
    (λ h : a < b, or.inl h)
    (λ h : a = b, or.inr (or.inl h)))
  (λ h : b ≤ a, or.elim (decidable.lt_or_eq_of_le h)
    (λ h : b < a, or.inr (or.inr h))
    (λ h : b = a, or.inr (or.inl h.symm)))

lemma le_of_not_lt {a b : α} (h : ¬ b < a) : a ≤ b :=
match lt_trichotomy a b with
| or.inl hlt          := le_of_lt hlt
| or.inr (or.inl heq) := heq ▸ le_refl a
| or.inr (or.inr hgt) := absurd hgt h
end

lemma le_of_not_gt {a b : α} : ¬ a > b → a ≤ b := le_of_not_lt

lemma lt_of_not_ge {a b : α} (h : ¬ a ≥ b) : a < b :=
lt_of_le_not_le ((le_total _ _).resolve_right h) h

lemma lt_or_le (a b : α) : a < b ∨ b ≤ a :=
if hba : b ≤ a then or.inr hba else or.inl $ lt_of_not_ge hba

lemma le_or_lt (a b : α) : a ≤ b ∨ b < a :=
(lt_or_le b a).swap

lemma lt_or_ge : ∀ (a b : α), a < b ∨ a ≥ b := lt_or_le
lemma le_or_gt : ∀ (a b : α), a ≤ b ∨ a > b := le_or_lt

lemma lt_or_gt_of_ne {a b : α} (h : a ≠ b) : a < b ∨ a > b :=
match lt_trichotomy a b with
| or.inl hlt          := or.inl hlt
| or.inr (or.inl heq) := absurd heq h
| or.inr (or.inr hgt) := or.inr hgt
end

lemma ne_iff_lt_or_gt {a b : α} : a ≠ b ↔ a < b ∨ a > b :=
⟨lt_or_gt_of_ne, λo, or.elim o ne_of_lt ne_of_gt⟩

lemma lt_iff_not_ge (x y : α) : x < y ↔ ¬ x ≥ y :=
⟨not_le_of_gt, lt_of_not_ge⟩

@[simp] lemma not_lt {a b : α} : ¬ a < b ↔ b ≤ a := ⟨le_of_not_gt, not_lt_of_ge⟩

@[simp] lemma not_le {a b : α} : ¬ a ≤ b ↔ b < a := (lt_iff_not_ge _ _).symm

instance (a b : α) : decidable (a < b) :=
linear_order.decidable_lt a b

instance (a b : α) : decidable (a ≤ b) :=
linear_order.decidable_le a b

instance (a b : α) : decidable (a = b) :=
linear_order.decidable_eq a b

lemma eq_or_lt_of_not_lt {a b : α} (h : ¬ a < b) : a = b ∨ b < a :=
if h₁ : a = b then or.inl h₁
else or.inr (lt_of_not_ge (λ hge, h (lt_of_le_of_ne hge h₁)))

instance : is_total_preorder α (≤) :=
{trans := @le_trans _ _, total := le_total}

/- TODO(Leo): decide whether we should keep this instance or not -/
instance is_strict_weak_order_of_linear_order : is_strict_weak_order α (<) :=
is_strict_weak_order_of_is_total_preorder lt_iff_not_ge

/- TODO(Leo): decide whether we should keep this instance or not -/
instance is_strict_total_order_of_linear_order : is_strict_total_order α (<) :=
{ trichotomous := lt_trichotomy }

/-- Perform a case-split on the ordering of `x` and `y` in a decidable linear order. -/
def lt_by_cases (x y : α) {P : Sort*}
  (h₁ : x < y → P) (h₂ : x = y → P) (h₃ : y < x → P) : P :=
if h : x < y then h₁ h else
if h' : y < x then h₃ h' else
h₂ (le_antisymm (le_of_not_gt h') (le_of_not_gt h))

lemma le_imp_le_of_lt_imp_lt {β} [preorder α] [linear_order β]
  {a b : α} {c d : β} (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
le_of_not_lt $ λ h', not_le_of_gt (H h') h

end linear_order
