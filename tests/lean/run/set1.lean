variables A : Type

instance : has_subset (set A) := ⟨λ s t, ∀ ⦃x⦄, x ∈ s → x ∈ t⟩

example (s₁ s₂ s₃ : set A) : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
assume h₁ h₂ a ains₁,
h₂ (h₁ ains₁)
