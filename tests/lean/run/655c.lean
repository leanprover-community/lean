universes u v w

-- fails to create a helper definition
-- TODO
-- def foldr_cps {α β γ : Sort*} (g : α → β → β) (z : β) : list α → (β → γ) → γ
-- | list.nil k := k z
-- | (list.cons x xs) k := foldr_cps xs (λz', k (g x z'))

-- succeeds
def foldr_cps' {α β γ : Sort*} (g : α → β → β) (z : β) (l : list α) : (β → γ) → γ :=
@list.rec_on α (λ _, (β → γ) → γ) l
  (λ k : β → γ, k z)
  (λ x xs r k, r (λ z', k (g x z')))

-- fails to create a helper definition
def foldr_cps'' {α : Type u} {β : Sort v} {γ : Sort w} (g : α → β → β) (z : β) : list α → (β → γ) → γ
| list.nil k := k z
| (list.cons x xs) k := foldr_cps'' xs (λz', k (g x z'))
