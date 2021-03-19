open function

class semiring (R : Type*) extends has_mul R, has_add R, has_one R, has_zero R.

class comm_semiring (R : Type*) extends semiring R.

class comm_ring (R : Type*) extends comm_semiring R.

class has_scalar' (R : Type*) (A : Type*) := (smul : R → A → A)

infixr ` • `:73 := has_scalar'.smul

structure ring_hom' (M : Type*) (N : Type*) [semiring M] [semiring N] :=
(to_fun : M → N)
(map_one' : to_fun 1 = 1)
(map_mul' : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)
(map_zero' : to_fun 0 = 0)
(map_add' : ∀ x y, to_fun (x + y) = to_fun x + to_fun y)

instance (α : Type*) (β : Type*) [semiring α] [semiring β] :
  has_coe_to_fun (ring_hom' α β) (λ _, α → β) :=
⟨λ f, ring_hom'.to_fun (f)⟩

class algebra' (R : Type*) (A : Type*) [comm_semiring R] [semiring A]
  extends has_scalar' R A, ring_hom' R A :=
(commutes' : ∀ r x, to_fun r * x = x * to_fun r)
(smul_def' : ∀ r x, r • x = to_fun r * x)

def algebra_map' (R : Type*) (A : Type*) [comm_semiring R] [semiring A] [algebra' R A] : ring_hom' R A :=
algebra'.to_ring_hom'

structure alg_hom' (R : Type*) (A : Type*) (B : Type*)
  [comm_semiring R] [semiring A] [semiring B] [algebra' R A] [algebra' R B] extends ring_hom' A B :=
(commutes' : ∀ r : R, to_fun (algebra_map' R A r) = algebra_map' R B r)

variables {R : Type*} {A : Type*} {B : Type*}
variables [comm_semiring R] [semiring A] [semiring B]
variables [algebra' R A] [algebra' R B]

instance : has_coe_to_fun (alg_hom' R A B) (λ _, A → B) := ⟨λ f, f.to_fun⟩

def quot.lift
  {R : Type} [comm_ring R]
  {A : Type} [comm_ring A] [algebra' R A]
  {B : Type*} [comm_ring B] [algebra' R B]
  {C : Type} [comm_ring C] [algebra' R C]
  (f : alg_hom' R A B) (hf : surjective f)
  (g : alg_hom' R A C) (hfg : ∀ a : A, f a = 0 → g a = 0) :
  alg_hom' R B C :=
{ to_fun := λ b, _,
  map_one' := _,
  map_mul' := _,
  map_zero' := _,
  map_add' := _,
  commutes' := _ }
