/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

/-
The elaborator tries to insert coercions automatically.
Only instances of has_coe type class are considered in the process.

Lean also provides a "lifting" operator: ↑a.
It uses all instances of has_lift type class.
Every has_coe instance is also a has_lift instance.

We recommend users only use has_coe for coercions that do not produce a lot
of ambiguity.

All coercions and lifts can be identified with the constant coe.

We use the has_coe_to_fun type class for encoding coercions from
a type to a function space.

We use the has_coe_to_sort type class for encoding coercions from
a type to a sort.
-/
prelude
import init.data.list.basic init.data.subtype.basic init.data.prod
universes u v

/-- Can perform a lifting operation `↑a`. -/
class has_lift (a : Sort u) (b : Sort v) :=
(lift : a → b)

class has_coe (a : Sort u) (b : Sort v) :=
(coe : a → b)

class has_coe_to_fun (a : Sort u) : Sort (max u (v+1)) :=
(F : a → Sort v) (coe : Π x, F x)

class has_coe_to_sort (a : Sort u) : Type (max u (v+1)) :=
(S : Sort v) (coe : a → S)

/- User level coercion operators -/

@[reducible] def coe {a : Sort u} {b : Sort v} [has_lift a b] : a → b :=
has_lift.lift

@[reducible] def coe_fn {a : Sort u} [has_coe_to_fun.{u v} a] : Π x : a, has_coe_to_fun.F.{u v} x :=
has_coe_to_fun.coe

@[reducible] def coe_sort {a : Sort u} [has_coe_to_sort.{u v} a] : a → has_coe_to_sort.S.{u v} a :=
has_coe_to_sort.coe

/- Notation -/

notation `↑`:max x:max := coe x

notation `⇑`:max x:max := coe_fn x

notation `↥`:max x:max := coe_sort x

universes u₁ u₂ u₃

instance coe_option {a : Type u} : has_coe a (option a) :=
⟨λ x, some x⟩

/- Every coercion is also a lift -/

instance coe_to_lift {a : Sort u} {b : Sort v} [has_coe a b] : has_lift a b :=
⟨has_coe.coe⟩

/- basic coercions -/

instance coe_bool_to_Prop : has_coe bool Prop :=
⟨λ y, y = tt⟩

/- Tactics such as the simplifier only unfold reducible constants when checking whether two terms are definitionally
   equal or a term is a proposition. The motivation is performance.
   In particular, when simplifying `p -> q`, the tactic `simp` only visits `p` if it can establish that it is a proposition.
   Thus, we mark the following instance as @[reducible], otherwise `simp` will not visit `↑p` when simplifying `↑p -> q`.
-/
@[reducible] instance coe_sort_bool : has_coe_to_sort bool :=
⟨Prop, λ y, y = tt⟩

instance coe_decidable_eq (x : bool) : decidable (coe x) :=
show decidable (x = tt), from bool.decidable_eq x tt

instance coe_subtype {a : Sort u} {p : a → Prop} : has_coe {x // p x} a :=
⟨subtype.val⟩

/- basic lifts -/

universes ua ua₁ ua₂ ub ub₁ ub₂

instance lift_fn {a₁ : Sort ua₁} {a₂ : Sort ua₂} {b₁ : Sort ub₁} {b₂ : Sort ub₂} [has_lift a₂ a₁] [has_lift b₁ b₂] : has_lift (a₁ → b₁) (a₂ → b₂) :=
⟨λ f x, ↑(f ↑x)⟩

instance lift_fn_range {a : Sort ua} {b₁ : Sort ub₁} {b₂ : Sort ub₂} [has_lift b₁ b₂] : has_lift (a → b₁) (a → b₂) :=
⟨λ f x, ↑(f x)⟩

instance lift_fn_dom {a₁ : Sort ua₁} {a₂ : Sort ua₂} {b : Sort ub} [has_lift a₂ a₁] : has_lift (a₁ → b) (a₂ → b) :=
⟨λ f x, f ↑x⟩

instance lift_pair {a₁ : Type ua₁} {a₂ : Type ub₂} {b₁ : Type ub₁} {b₂ : Type ub₂} [has_lift a₁ a₂] [has_lift b₁ b₂] : has_lift (a₁ × b₁) (a₂ × b₂) :=
⟨λ p, p.map coe coe⟩

instance lift_pair₁ {a₁ : Type ua₁} {a₂ : Type ua₂} {b : Type ub} [has_lift a₁ a₂] : has_lift (a₁ × b) (a₂ × b) :=
⟨λ p, p.map coe (λ x, x)⟩

instance lift_pair₂ {a : Type ua} {b₁ : Type ub₁} {b₂ : Type ub₂} [has_lift b₁ b₂] : has_lift (a × b₁) (a × b₂) :=
⟨λ p, p.map (λ x, x) coe⟩

instance lift_list {a : Type u} {b : Type v} [has_lift a b] : has_lift (list a) (list b) :=
⟨λ l, l.map coe⟩
