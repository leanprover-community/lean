@[class]
def fact (p : Prop) := p

example {P Q R : Prop} [fact (P → Q → R)] : fact (P → Q → R) :=
by apply_instance