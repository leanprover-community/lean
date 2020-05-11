-- Generalized version of type classes with type class parameters that are
-- common in mathlib.

-- a could be topological_space, b could be ring, ...,
-- y is topological_ring, and z is topological_group

class a (α : Type)
instance a1 (α) : a α := ⟨⟩
instance a2 (α) : a α := ⟨⟩
instance a3 (α) : a α := ⟨⟩
instance a4 (α) : a α := ⟨⟩
instance a5 (α) : a α := ⟨⟩
instance a6 (α) : a α := ⟨⟩
instance a7 (α) : a α := ⟨⟩
instance a8 (α) : a α := ⟨⟩
instance a9 (α) : a α := ⟨⟩
instance a0 (α) : a α := ⟨⟩

class b (α : Type)
instance b1 (α) : b α := ⟨⟩
instance b2 (α) : b α := ⟨⟩
instance b3 (α) : b α := ⟨⟩
instance b4 (α) : b α := ⟨⟩
instance b5 (α) : b α := ⟨⟩
instance b6 (α) : b α := ⟨⟩
instance b7 (α) : b α := ⟨⟩
instance b8 (α) : b α := ⟨⟩
instance b9 (α) : b α := ⟨⟩
instance b0 (α) : b α := ⟨⟩

class c (α : Type)
instance c1 (α) : c α := ⟨⟩
instance c2 (α) : c α := ⟨⟩
instance c3 (α) : c α := ⟨⟩
instance c4 (α) : c α := ⟨⟩
instance c5 (α) : c α := ⟨⟩
instance c6 (α) : c α := ⟨⟩
instance c7 (α) : c α := ⟨⟩
instance c8 (α) : c α := ⟨⟩
instance c9 (α) : c α := ⟨⟩
instance c0 (α) : c α := ⟨⟩

class d (α : Type)
instance d1 (α) : d α := ⟨⟩
instance d2 (α) : d α := ⟨⟩
instance d3 (α) : d α := ⟨⟩
instance d4 (α) : d α := ⟨⟩
instance d5 (α) : d α := ⟨⟩
instance d6 (α) : d α := ⟨⟩
instance d7 (α) : d α := ⟨⟩
instance d8 (α) : d α := ⟨⟩
instance d9 (α) : d α := ⟨⟩
instance d0 (α) : d α := ⟨⟩

class e (α : Type)
instance e1 (α) : e α := ⟨⟩
instance e2 (α) : e α := ⟨⟩
instance e3 (α) : e α := ⟨⟩
instance e4 (α) : e α := ⟨⟩
instance e5 (α) : e α := ⟨⟩
instance e6 (α) : e α := ⟨⟩
instance e7 (α) : e α := ⟨⟩
instance e8 (α) : e α := ⟨⟩
instance e9 (α) : e α := ⟨⟩
instance e0 (α) : e α := ⟨⟩

class f (α : Type)
instance f1 (α) : f α := ⟨⟩
instance f2 (α) : f α := ⟨⟩
instance f3 (α) : f α := ⟨⟩
instance f4 (α) : f α := ⟨⟩
instance f5 (α) : f α := ⟨⟩
instance f6 (α) : f α := ⟨⟩
instance f7 (α) : f α := ⟨⟩
instance f8 (α) : f α := ⟨⟩
instance f9 (α) : f α := ⟨⟩
instance f0 (α) : f α := ⟨⟩

class g (α : Type)
instance g1 (α) : g α := ⟨⟩
instance g2 (α) : g α := ⟨⟩
instance g3 (α) : g α := ⟨⟩
instance g4 (α) : g α := ⟨⟩
instance g5 (α) : g α := ⟨⟩
instance g6 (α) : g α := ⟨⟩
instance g7 (α) : g α := ⟨⟩
instance g8 (α) : g α := ⟨⟩
instance g9 (α) : g α := ⟨⟩
instance g0 (α) : g α := ⟨⟩

class y (α : Type) [a α] [b α] [c α] [d α] [e α] [f α] [g α]

instance y1 (α) : y α := ⟨⟩

class z (α : Type) [a α] [b α] [c α] [d α] [e α] [f α]

instance z.to_y (α : Type) [a α] [b α] [c α] [d α] [e α] [f α] [g α] [z α] : y α :=
⟨⟩

example : y unit :=
by apply_instance