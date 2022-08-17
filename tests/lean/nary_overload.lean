prelude

constant {l} vec : Type l → Type l
constant {l} lst : Type l → Type l
constant vec.nil {A : Type} : vec A
constant lst.nil {A : Type} : lst A
constant vec.cons {A : Type} : A → vec A → vec A
constant lst.cons {A : Type} : A → lst A → lst A

notation (name := list1) `[` l:(foldr `, ` (h t, vec.cons h t) vec.nil `]`) := l
notation (name := list2) `[` l:(foldr `, ` (h t, lst.cons h t) lst.nil `]`) := l

constant A : Type
variables a b c : A

#check [a, b, c]
#check ([a, b, c] : vec A)
#check ([a, b, c] : lst A)
set_option pp.all true
#check ([a, b, c] : vec A)
#check ([a, b, c] : lst A)
