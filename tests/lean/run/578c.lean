def fin.last (n : ℕ) : fin (n+1) := ⟨_, n.lt_succ_self⟩
set_option trace.tactic.cases true
example (i_val : ℕ) (i_property : i_val < 1)
  (h : (⟨i_val, i_property⟩ : fin 1) = fin.last 0) : false :=
by { cases h, sorry }
