/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.interactive
import init.control.lawful

universes u v

structure set (α : Type u) : Type u :=
of :: (contains : α → Prop)

namespace set
variables {α : Type u} {β : Type v}

instance : has_mem α (set α) :=
⟨λ x s, s.contains x⟩

instance : has_subset (set α) :=
⟨λ s₁ s₂, ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂⟩

instance : has_sep α (set α) :=
⟨λ p s, { a | a ∈ s ∧ p a}⟩

instance : has_emptyc (set α) :=
⟨{ a | false }⟩

def univ : set α :=
{ a | true }

instance : has_insert α (set α) :=
⟨λ a s, { b | b = a ∨ b ∈ s }⟩

instance : has_singleton α (set α) := ⟨λ a, { b | b = a }⟩

protected lemma ext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
begin
  cases a with a,
  cases b with b,
  simp [show a = b, from funext (λ x, propext (h _))]
end

instance : is_lawful_singleton α (set α) :=
⟨λ a, set.ext (λ x, or_false _)⟩

instance : has_union (set α) :=
⟨λ s₁ s₂, { a | a ∈ s₁ ∨ a ∈ s₂ }⟩

instance : has_inter (set α) :=
⟨λ s₁ s₂, { a | a ∈ s₁ ∧ a ∈ s₂ }⟩

def compl (s : set α) : set α :=
{a | a ∉ s}

instance : has_sdiff (set α) :=
⟨λ s t, { a ∈ s | a ∉ t }⟩

def powerset (s : set α) : set (set α) :=
{t | t ⊆ s}
prefix `𝒫`:100 := powerset

@[reducible]
def sUnion (s : set (set α)) : set α := {t | ∃ a ∈ s, t ∈ a}
prefix `⋃₀`:110 := sUnion

def image (f : α → β) (s : set α) : set β :=
{b | ∃ a, a ∈ s ∧ f a = b}

instance : functor set :=
{ map := @set.image }

instance : is_lawful_functor set :=
{ id_map := λ _ s, set.ext $ λ b, ⟨λ ⟨_, sb, rfl⟩, sb, λ sb, ⟨_, sb, rfl⟩⟩,
  comp_map := λ _ _ _ g h s, set.ext $ λ c,
    ⟨λ ⟨a, ⟨h₁, h₂⟩⟩, ⟨g a, ⟨⟨a, ⟨h₁, rfl⟩⟩, h₂⟩⟩,
     λ ⟨b, ⟨⟨a, ⟨h₁, h₂⟩⟩, h₃⟩⟩, ⟨a, ⟨h₁, by dsimp; cc⟩⟩⟩ }

end set
