structure foo (H : Type) :=
(foo : H)

variables {H : Type} (G : foo H)

structure foo.bar (G : foo H) (P : H → Prop) : Prop :=
(bar : P G.foo)

example {P : H → Prop} (h : G.bar P) : true := trivial

structure foo.bar' (P : H → Prop) : Prop :=
(bar : P G.foo)

set_option pp.annotations true
set_option pp.all true
#print foo.bar
#print foo.bar'

example {P : H → Prop} (h : G.bar' P) : true := trivial
