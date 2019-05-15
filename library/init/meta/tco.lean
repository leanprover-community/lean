prelude
import init.category init.meta.local_context init.meta.tactic

/-- type_context_old monad. -/
meta constant tco : Type → Type

namespace tco
variables {α β : Type}
protected meta constant bind : tco α → (α → tco β) → tco β
protected meta constant pure : α → tco α
protected meta constant fail : format → tco α
protected meta def failure : tco α := tco.fail ""
meta instance : monad tco := {bind := @tco.bind, pure := @tco.pure}
meta instance : monad_fail tco := {fail := λ α, tco.fail ∘ to_fmt}

/- [TODO] -/ meta constant get_env : tco environment

/- [TODO] -/ meta constant whnf : expr → tco expr

meta constant is_def_eq (e₁ e₂ : expr) (approx := ff)  :  tco bool
meta constant unify (e₁ e₂ : expr) (approx := ff)  : tco bool
/-- Infer the type of the given expr. Not including a typecheck. -/
meta constant infer : expr → tco expr
/-- Asks the kernel whether the given expression typechecks in this context. -/
/- [TODO] -/ meta constant check : expr → tco bool
/- [TODO] -/ meta constant is_stuck : expr → tco bool
/- [TODO] many more reductions such as zeta, beta, head-beta etc. -/

/-- Add a local to the tco local context. -/
/- [TODO] -/ meta constant push_local (pp_name : name) (type : expr) (bi := binder_info.default) : tco expr
/- [TODO] -/ meta constant pop_local : tco unit

/-- Get the local context of the tco. -/
/- [TODO] -/ meta constant get_local_context : tco lc

/- METAVARIABLES -/

meta constant mk_mvar (pp_name : name) (type : expr) (context : lc) : tco expr
/-- Set the mvar to the following assignments.
    Works for temporary metas too.
    [WARNING] `assign` is **unsafe**:
     - No typecheck is done before assignment.
     - If the metavariable is already assigned this will clobber the assignment.
     - It will not stop you from assigning an metavariable to itself or creating cycles of metavariable assignments.
       These will manifest as 'deep recursion' exceptions when `instantiate_mvars` is used.
    You can avoid the unsafety by using `unify` instead.
-/
meta constant assign (mvar : expr) (assignment : expr) : tco unit
/- [TODO] -/ meta constant level.assign (mvar : level) (assignment : level) : tco unit
/-- Returns true if the mvar is declared. Also works for temporary mvars. -/
meta constant mvar_is_declared (mvar : expr) : tco bool
/- [TODO] -/ meta constant is_assigned (mvar : expr) : tco bool
/- [TODO] -/ meta constant get_context (mvar : expr) : tco lc
/-- Works for temps too.-/
/- [TODO] -/ meta constant get_assignment (mvar : expr) : tco expr

meta constant instantiate_mvars : expr → tco expr
meta constant level.instantiate_mvars : level → tco level

/- [TODO] -/ meta constant is_mvar (e : expr) : tco bool
/- [TODO] -/ meta constant is_tmp_mvar (mvar : expr) : tco bool
/- [TODO] -/ meta constant is_regular_mvar (mvar : expr) : tco bool

/-- Run the given `tco` monad in a temporary mvar scope.
Doing this twice will push the old tmp_mvar assignments to a stack.
So it is safe to do this whether or not you are already in tmp mode. -/
meta constant tmp_mode (n_uvars n_mvars : nat) : tco α → tco α

/-- Returns true when we are in temp mode. -/
meta constant in_tmp_mode : tco bool
/-- Number of temporary metavariables that are active in the current scope. -/
/- [TODO] -/ meta constant tmp_count : tco nat
/- [TODO] -/ meta constant tmp_is_assigned : nat → tco bool
/- [TODO] -/ meta constant tmp_get_assignment : nat → tco expr

/- [TODO] -/ meta constant level.tmp_count : tco nat
/- [TODO] -/ meta constant level.tmp_is_assigned : nat → tco bool
/- [TODO] -/ meta constant level.tmp_get_assignment : nat → tco level

/- BACKTRACKING -/

/-- Run the provided tco within a backtracking scope.
    This means that any changes to the metavariable context will not be committed if the
    inner monad fails to run.
-/
/- [TODO] -/ meta constant try {α : Type} : tco α → tco (option α)

meta constant run (inner : tco α) (tr := tactic.transparency.semireducible) : tactic α

end tco

-- meta constant expr.delayed_abstraction : expr → list expr → expr
