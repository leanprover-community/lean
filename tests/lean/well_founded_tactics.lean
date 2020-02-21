variables {α : Type} {lt : α → α → Prop} [decidable_rel lt]

def merge : list α → list α → list α
| []       l'        := l'
| l        []        := l
| (a :: l) (b :: l') := if lt a b then a :: merge l (b :: l') else b :: merge (a :: l) l'
