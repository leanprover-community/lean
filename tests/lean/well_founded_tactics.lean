variables {α : Type} {lt : α → α → Prop} [decidable_rel lt]

def merge : list α → list α → list α
| []       l'        := l'
| l        []        := l
| (a :: l) (b :: l') := if lt a b then a :: merge l (b :: l') else b :: merge (a :: l) l'

def foo : Π (s : ℕ), ℕ
| 0 := 1
| (nat.succ s) := foo s + 1
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨_, measure_wf id⟩] }
