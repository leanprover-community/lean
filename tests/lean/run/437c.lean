example (a : ℕ) : true :=
begin
  have : ∀ n, n ≥ 0 → a ≤ a,
  { exact λ _ _, le_refl a },
  trivial
end
