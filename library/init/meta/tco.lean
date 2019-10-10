prelude
import init.category init.meta.local_context init.meta.tactic init.meta.fun_info

/-- A monad that exposes the functionality of the C++ class `type_context_old`.
    The idea is that the methods in `tco` are more powerful but _unsafe_ in the
    sense that you can create terms that do not typecheck or that are infinitely descending.
    Under the hood, `tco` is implemented as a reader monad, with a mutable `type_context_old` object.
     -/
meta constant tco : Type → Type

namespace tco
variables {α β : Type}
protected meta constant bind : tco α → (α → tco β) → tco β
protected meta constant pure : α → tco α
protected meta constant fail : format → tco α
protected meta def failure : tco α := tco.fail ""
meta instance : monad tco := {bind := @tco.bind, pure := @tco.pure}
meta instance : monad_fail tco := {fail := λ α, tco.fail ∘ to_fmt}

meta constant get_env : tco environment

meta constant whnf : expr → tco expr

meta constant is_def_eq (e₁ e₂ : expr) (approx := ff)  :  tco bool
meta constant unify (e₁ e₂ : expr) (approx := ff)  : tco bool
/-- Infer the type of the given expr. Inferring the type does not mean that it typechecks. Will fail if type can't be inferred. -/
meta constant infer : expr → tco expr
/-- A stuck expression `e` is an expression that _would_ reduce,
except that a metavariable is present that prevents the reduction.
Returns the metavariable which is causing the stuckage.
For example, `@has_add.add nat ?m a b` can't project because `?m` is not given.
-/
meta constant is_stuck : expr → tco (option expr)

/-- Add a local to the tco local context. -/
meta constant push_local (pp_name : name) (type : expr) (bi := binder_info.default) : tco expr
meta constant pop_local : tco unit
/-- Get the local context of the tco. -/
meta constant get_local_context : tco lc

/- METAVARIABLES -/

meta constant mk_mvar (pp_name : name) (type : expr) (context : option lc := none) : tco expr
/-- Iterate over all mvars in the mvar context. -/
meta constant fold_mvars {α : Type} (f : α → expr → tco α) : α → tco α
meta def list_mvars : tco (list expr) := fold_mvars (λ l x, pure $ x :: l) []
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
meta constant level.assign (mvar : level) (assignment : level) : tco unit
/-- Returns true if the given expression is a declared local constant or a declared metavariable. -/
meta constant is_declared (e : expr) : tco bool
meta constant is_assigned (mvar : expr) : tco bool
meta constant get_context (mvar : expr) : tco lc
/-- Works for temps too.-/
meta constant get_assignment (mvar : expr) : tco expr

meta constant instantiate_mvars : expr → tco expr
meta constant level.instantiate_mvars : level → tco level

meta constant is_tmp_mvar (mvar : expr) : tco bool
meta constant is_regular_mvar (mvar : expr) : tco bool

/-- Run the given `tco` monad in a temporary mvar scope. ↝
Doing this twice will push the old tmp_mvar assignments to a stack.
So it is safe to do this whether or not you are already in tmp mode. -/
meta constant tmp_mode (n_uvars n_mvars : nat) : tco α → tco α

/-- Returns true when we are in temp mode. -/
meta constant in_tmp_mode : tco bool
meta constant tmp_is_assigned : nat → tco bool
meta constant tmp_get_assignment : nat → tco expr

meta constant level.tmp_is_assigned : nat → tco bool
meta constant level.tmp_get_assignment : nat → tco level

/-- Replace each metavariable in the given expression with a temporary metavariable. -/
meta constant to_tmp_mvars : expr → tco (expr × list level × list expr)
meta constant mk_tmp_mvar (index : nat) (type : expr): expr
meta constant level.mk_tmp_mvar (index : nat) : level

/-- Run the provided tco within a backtracking scope.
    This means that any changes to the metavariable context will not be committed if the
    inner monad fails.
    [warning]: the local context modified by `push_local` and `pop_local`
    is not affected by `try`. Any unpopped locals will be present after the `try` even if the inner `tco` failed.
-/
meta constant try {α : Type} : tco α → tco (option α)

meta def orelse {α : Type} : tco α → tco α → tco α
| x y := try x >>= λ x, option.rec y pure x

meta instance tco_alternative : alternative tco := {
    failure := λ α, tco.fail "failed",
    orelse := λ α x y, tco.orelse x y
}

meta constant run (inner : tco α) (tr := tactic.transparency.semireducible) : tactic α

meta def trace {α} [has_to_format α] : α → tco unit | a :=
   pure $ _root_.trace_fmt (to_fmt a) (λ u, ())

meta def print_mvars : tco unit := do
    mvs ← list_mvars,
    mvs ← pure $ mvs.map (λ x, match x with (expr.mvar _ pp _) := to_fmt pp | _ := "" end),
    trace mvs

meta constant get_fun_info (f : expr) (nargs : option nat := none) : tco fun_info

end tco

-- meta constant expr.delayed_abstraction : expr → list expr → expr
