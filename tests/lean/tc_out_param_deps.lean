prelude
import init.core

class semiring (G : Type*) := (one : G)

instance : semiring nat := ⟨1⟩

class add_monoid_hom_class (F : Type*) (H : out_param Type*) [semiring H] :=
(coe : F → nat → H)
(ext_nat : ∀ (f g : F), coe f 1 = coe g 1 → f = g)

open add_monoid_hom_class

class semiring_hom_class (F : Type*) (H : out_param Type*) [semiring H]
  extends add_monoid_hom_class F H :=
(map_one : ∀ (f : F), coe f 1 = semiring.one)

-- Ensure `H` can be inferred through the `out_param` of `semiring_hom_class`,
-- even though `semiring H` is a non-out_param depending on it.
lemma semiring_hom_class.ext_nat {F : Type*} {H : Type*} [semiring H]
  [semiring_hom_class F H] (f g : F) : f = g :=
add_monoid_hom_class.ext_nat f g $
  (semiring_hom_class.map_one f).trans (semiring_hom_class.map_one g).symm
