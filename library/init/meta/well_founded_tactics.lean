/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta

protected def {u v} psum.alt.sizeof
  {α : Type u} {β : Type v} [has_sizeof α] [has_sizeof β] : psum α β → ℕ
| (psum.inl a) := sizeof a
| (psum.inr b) := sizeof b

@[reducible]
protected def {u v} psum.has_sizeof_alt
  (α : Type u) (β : Type v) [has_sizeof α] [has_sizeof β] : has_sizeof (psum α β) :=
⟨psum.alt.sizeof⟩

namespace well_founded_tactics
open tactic

meta def mk_alt_sizeof : expr → expr
| (expr.app (expr.app (expr.app (expr.app (expr.const ``psum.has_sizeof l) α) β) iα) iβ) :=
  (expr.const ``psum.has_sizeof_alt l : expr) α β iα (mk_alt_sizeof iβ)
| e := e

meta def default_rel_tac (e : expr) (eqns : list expr) : tactic unit :=
do tgt ← target,
  rel ← mk_instance tgt,
  exact $ match e, rel with
    expr.local_const _ (name.mk_string "_mutual" _) _ _,
    expr.app e@`(@has_well_founded_of_has_sizeof _) sz := e (mk_alt_sizeof sz)
  | _, _ := rel
  end

end well_founded_tactics

/-- Arguments for `using_well_founded`

  The two arguments are: a local representing the function being defined by well
  founded recursion, and a list of recursive equations.
  The equations can be used to decide which well founded relation should be used.

  The tactic `dec_tac` has to synthesize decreasing proofs.
-/
meta structure well_founded_tactics :=
(rel_tac : expr → list expr → tactic unit := well_founded_tactics.default_rel_tac)
(dec_tac : tactic unit := tactic.assumption)

meta def well_founded_tactics.default : well_founded_tactics :=
{}
