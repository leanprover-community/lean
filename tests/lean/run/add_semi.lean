class add_semigroup (A : Type*) extends has_add A :=
(add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
class add_comm_semigroup (A : Type*) extends add_semigroup A :=
(add_comm : ∀ a b : A, a + b = b + a)

section
  universe variables u
  variable {A : Type u}

  example [add_semigroup A] (a : A) : a + a = a + a := rfl
  example [add_comm_semigroup A] (a : A) : a + a = a + a := rfl
end

section
  variable {A : Type}

  example [add_semigroup A] (a : A) : a + a = a + a := rfl
  example [add_comm_semigroup A] (a : A) : a + a = a + a := rfl
end
