class A (α : Type)

class B (α : Type) extends A α
#print B.to_A

section prio
set_option extends_priority 37
class C (α : Type) extends B α
end prio
#print C.to_B

class D (α : Type) extends C α
#print D.to_C


set_option old_structure_cmd true


class A' (α : Type)

class B' (α : Type) extends A' α
#print B'.to_A'

section prio
set_option extends_priority 37
class C' (α : Type) extends B' α
end prio
#print C'.to_B'

class D' (α : Type) extends C' α
#print D'.to_C'
