-- verify that class resolution is done from right to left

class a (α : Type) (x : bool)
class b (α : Type) (x : bool)
class c (α : Type)

instance (α) : a α tt := ⟨⟩
instance (α) : b α tt := ⟨⟩
instance b.to_c (α x) [a α x] [b α x] : c α := ⟨⟩

-- make all type-class resolution queries for `a α ff` fail
instance (α) [a α ff] : a α ff := ‹a α ff›

set_option trace.class_instances true
example (α) : c α :=
by apply_instance

