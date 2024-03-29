def foo := ℕ

namespace foo
instance : has_add foo := nat.has_add
end foo

-- verify that `foo.has_add` was created
example := foo.has_add

namespace category_theory

def functor : Type := ℕ
class is_right_adjoint (F : functor) : Prop
class preserves_limits (F : functor) : Prop
def forgetful_functor : functor := nat.zero

instance : is_right_adjoint forgetful_functor := ⟨⟩

instance : is_right_adjoint nat.zero := ⟨⟩

-- satisfy the inhabited linter
instance : inhabited functor := ⟨forgetful_functor⟩

end category_theory

-- here we end up with a name with a repeated component
section
open category_theory
instance : category_theory.preserves_limits forgetful_functor := ⟨⟩
end

class lie_algebra (α : Type) : Type :=
(bracket : α → α → α)

namespace lie_algebra

instance : lie_algebra ℤ := ⟨λ x y, x * y - y * x⟩

def gl : Type := unit
instance : lie_algebra gl := ⟨λ _ _, ()⟩

end lie_algebra

class moo (α : Type*)
class zoo (β : Type*)

namespace zoo
-- Every zoo is a moo.
instance (β : Type*) [zoo β] : moo β := ⟨⟩
end zoo

-- A boo is a bundled moo.
structure boo : Type 1 :=
(β : Type)
[is_zoo : moo β]

instance : has_coe_to_sort boo _ := ⟨boo.β⟩

namespace boo
-- Instance naming for variable arguments works (generating `boo.moo`)
-- even if the variable is actually being implicitly coerced to something else.
instance (b : boo) : moo b := ⟨⟩

-- Instance naming works for projections
instance (b : boo) : moo b.β := ⟨⟩
example := boo.β.moo
end boo

-- Instance naming works for explicit type ascriptions
instance : moo (@set ℕ : Type) := ⟨⟩
example := set.moo

-- also for sorts
instance : moo Type := ⟨⟩
example := sort.moo

-- and pis
instance : moo (ℕ → ℕ) := ⟨⟩
example := pi.moo

section
parameter (n : ℕ)
def cow := fin n
-- and parameters
instance : moo cow := ⟨⟩
example := cow.moo
end

example := category_theory.forgetful_functor.is_right_adjoint
example := category_theory.nat.zero.is_right_adjoint
example := category_theory.functor.inhabited
example := category_theory.forgetful_functor.category_theory.preserves_limits
example := lie_algebra.int.lie_algebra
example := lie_algebra.gl.lie_algebra
example := zoo.moo
example := boo.moo
example := boo.has_coe_to_sort
