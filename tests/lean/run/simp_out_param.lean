prelude
import init.meta.interactive

namespace unbundled

class broken₁ (A : Type*) :=
(f : A → A)
open broken₁

class broken₂ (A : Type*) (a : out_param $ A)
  -- The following doesn't need to be an `out_param` when #657 is merged:
  [out_param $ broken₁ A] :=
(f_eq : ∀ x, f x = a)
open broken₂

-- Even if the goal doesn't contain an instance of `broken₂`, the parameter `a`
-- to `f_eq` should still be inferrable since it's an `out_param`.
example (A : Type*) (a : A) [broken₁ A] [broken₂ A a] (x : A) : f x = a :=
by rewrite [f_eq]

example (A : Type*) (a : A) [broken₁ A] [broken₂ A a] (x : A) : f x = a :=
by simp only [f_eq]
-- Previous error: "simplify tactic failed to simplify", `f_eq` failed because "fail to instantiate emetas"

end unbundled
