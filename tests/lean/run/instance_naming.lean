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

example := category_theory.forgetful_functor.is_right_adjoint
example := category_theory.nat.zero.is_right_adjoint
example := category_theory.functor.inhabited
example := category_theory.forgetful_functor.category_theory.preserves_limits
