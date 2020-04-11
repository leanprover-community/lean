import .html

structure widget (α : Type) :=
(β : Type)
(σ : Type)
(init   : σ)
(update (state : σ) (action : β) : (σ × α))
(view   (state : σ) : html β)

meta constant tactic.save_widget : pos → (tactic_state → widget unit) → tactic unit
