@[irreducible] instance : has_zero string := ⟨""⟩

class foo (s : string) : Prop
instance string.foo : foo 0 := ⟨⟩

#eval tactic.mk_instance `(foo "")