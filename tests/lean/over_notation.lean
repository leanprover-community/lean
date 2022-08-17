constant f : nat → nat → nat
constant g : string → string → string

infix (name := f) ` & `:60 := f
infix (name := g) ` & `:60 := g

set_option pp.notation false

#check 0 & 1
#check "a" & "b"
#check tt & ff

notation (name := list1) `[[`:max l:(foldr `, ` (h t, f h t) 0 `]]`:0) := l
notation (name := list2) `[[`:max l:(foldr `, ` (h t, g h t) "" `]]`:0) := l

#check [[ (1:nat), 2, 3 ]]
#check [[ "a", "b", "c" ]]
