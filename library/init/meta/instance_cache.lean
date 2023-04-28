/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import init.meta.tactic init.meta.interactive

/-!
# Instance cache tactics

For performance reasons, Lean does not automatically update its database
of class instances during a proof. The group of tactics in this file
helps to force such updates.

-/
open lean.parser
open interactive interactive.types

local postfix `?`:9001 := optional
local postfix *:9001 := many

namespace tactic
/-- Reset the instance cache for the main goal. -/
meta def reset_instance_cache : tactic unit := do
unfreeze_local_instances,
freeze_local_instances

/-- Unfreeze the local instances while executing `tac` on the main goal. -/
meta def unfreezing {α} (tac : tactic α) : tactic α :=
focus1 $ unfreeze_local_instances *> tac <* all_goals freeze_local_instances

/--
Unfreeze local instances while executing `tac`,
if the passed expression is amongst the frozen instances.
-/
meta def unfreezing_hyp (h : expr) (tac : tactic unit) : tactic unit :=
do frozen ← frozen_local_instances,
   if h ∈ frozen.get_or_else [] then unfreezing tac else tac

namespace interactive

/--
`unfreezingI { tac }` executes tac while temporarily unfreezing the instance cache.
-/
meta def unfreezingI (tac : itactic) :=
focus1 $
  propagate_tags unfreeze_local_instances *> tac <*
  all_goals (propagate_tags freeze_local_instances)

/-- Reset the instance cache. This allows any new instances
added to the context to be used in typeclass inference. -/
meta def resetI := propagate_tags reset_instance_cache

/-- Like `revert`, but can also revert instance arguments. -/
meta def revertI (ids : parse ident*) : tactic unit :=
unfreezingI (revert ids)

/-- Like `subst`, but can also substitute in instance arguments. -/
meta def substI (q : parse texpr) : tactic unit :=
unfreezingI (subst q)

/-- Like `cases`, but can also be used with instance arguments. -/
meta def casesI (p : parse cases_arg_p) (q : parse with_ident_list) : tactic unit :=
unfreezingI (cases p q)

/-- Like `intro`, but uses the introduced variable
in typeclass inference. -/
meta def introI (p : parse ident_?) : tactic unit :=
intro p >> resetI

/-- Like `intros`, but uses the introduced variable(s)
in typeclass inference. -/
meta def introsI (p : parse ident_*) : tactic unit :=
intros p >> resetI

/-- Used to add typeclasses to the context so that they can
be used in typeclass inference. The syntax is the same as `have`. -/
meta def haveI (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse (tk ":=" *> texpr)?) :
  tactic unit :=
do h ← match h with
  | none   := get_unused_name "_inst"
  | some a := return a
  end,
  «have» (some h) q₁ q₂,
  match q₂ with
  | none    := swap >> resetI >> swap
  | some p₂ := resetI
  end

/-- Used to add typeclasses to the context so that they can
be used in typeclass inference. The syntax is the same as `let`. -/
meta def letI
  (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) :
  tactic unit :=
do h ← match h with
  | none   := get_unused_name "_inst"
  | some a := return a
  end,
  «let» (some h) q₁ q₂,
  match q₂ with
  | none    := swap >> resetI >> swap
  | some p₂ := resetI
  end

/-- Like `exact`, but uses all variables in the context
for typeclass inference. -/
meta def exactI (q : parse texpr) : tactic unit :=
resetI >> exact q

end interactive
end tactic
