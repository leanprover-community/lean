/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.interactive
import init.control.lawful

universes u v

/-- A set of elements of type `α`; implemented as a predicate `α → Prop`. -/
def set (α : Type u) := α → Prop

/-- The set `{x | p x}` of elements satisfying the predicate `p`. -/
def set_of {α : Type u} (p : α → Prop) : set α := p

namespace set

variables {α : Type u}

instance has_mem : has_mem α (set α) := ⟨λ x s, s x⟩

@[simp] lemma mem_set_of_eq {x : α} {p : α → Prop} : x ∈ {y | p y} = p x := rfl

instance : has_emptyc (set α) := ⟨{x | false}⟩

/-- The set that contains all elements of a type. -/
def univ : set α := {x | true}

instance : has_insert α (set α) := ⟨λ a s, {b | b = a ∨ b ∈ s}⟩

instance : has_singleton α (set α) := ⟨λ a, {b | b = a}⟩

instance : has_sep α (set α) := ⟨λ p s, {x | x ∈ s ∧ p x}⟩

instance : is_lawful_singleton α (set α) :=
⟨λ a, funext $ λ b, propext $ or_false _⟩

end set
