class A {α : Type*} (x : α)

instance {α : Type*} {p : α → Prop} (x : subtype p) : A x.1 := A.mk

example := @subtype.field_1.A

instance {α : Type*} {p : α → Prop} (x : subtype p) : A x.val := A.mk

example := @subtype.val.A
