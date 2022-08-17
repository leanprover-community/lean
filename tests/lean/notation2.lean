--
inductive List (T : Type) : Type
| nil {} : List
| cons   : T → List → List
open List
notation (name := cons2) h :: t  := cons h t
notation (name := list2) `[` l:(foldr `,` (h t, cons h t) nil) `]` := l
infixr (name := cons) `::` := cons
#check (1:nat) :: 2 :: nil
#check (1:nat) :: 2 :: 3 :: 4 :: 5 :: nil
#print ]
