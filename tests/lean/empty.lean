--
open inhabited nonempty classical

noncomputable lemma v1 : Prop := epsilon (λ x : Prop, true)
inductive Empty : Type
noncomputable definition v2 : Empty := epsilon (λ x, true)
