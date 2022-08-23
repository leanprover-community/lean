prelude
definition Prop : Sort.{1} := Sort.{0}
constant eq : forall {A : Type}, A → A → Prop
constant N : Type
constants a b c : N
infix `=`:50 := eq
#check a = b

constant f : Prop → N → N
constant g : N → N → N
precedence `+`:50
infixl (name := f) + := f
infixl (name := g) + := g
#check a + b + c
constant p : Prop
#check p + a + b + c
