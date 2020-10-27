prelude
import init.control.monad init.meta.local_context init.meta.tactic init.meta.fun_info
namespace tactic.unsafe
/-- A monad that exposes the functionality of the C++ class `type_context_old`.
The idea is that the methods to `type_context` are more powerful but _unsafe_ in the
sense that you can create terms that do not typecheck or that are infinitely descending.
Under the hood, `type_context` is implemented as a reader monad, with a mutable `type_context` object.
-/
meta constant type_context : Type → Type
namespace type_context
variables {α β : Type}
protected meta constant bind : type_context α → (α → type_context β) → type_context β
protected meta constant pure : α → type_context α
protected meta constant fail : format → type_context α
protected meta def failure : type_context α := type_context.fail ""
meta instance : monad type_context := {bind := @type_context.bind, pure := @type_context.pure}
meta instance : monad_fail type_context := {fail := λ α, type_context.fail ∘ to_fmt}
meta constant get_env : type_context environment
meta constant whnf : expr → type_context expr
meta constant is_def_eq (e₁ e₂ : expr) (approx := ff) : type_context bool
meta constant unify (e₁ e₂ : expr) (approx := ff) : type_context bool
/-- Infer the type of the given expr. Inferring the type does not mean that it typechecks.
Will fail if type can't be inferred. -/
meta constant infer : expr → type_context expr
/-- A stuck expression `e` is an expression that _would_ reduce,
except that a metavariable is present that prevents the reduction.
Returns the metavariable which is causing the stuckage.
For example, `@has_add.add nat ?m a b` can't project because `?m` is not given. -/
meta constant is_stuck : expr → type_context (option expr)
/-- Add a local to the tc local context. -/
meta constant push_local (pp_name : name) (type : expr) (bi := binder_info.default) : type_context expr
meta constant pop_local : type_context unit
/-- Get the local context of the type_context. -/
meta constant get_local_context : type_context local_context
/-- Create and declare a new metavariable. If the local context is not given then it will use the current local context. -/
meta constant mk_mvar (pp_name : name) (type : expr) (context : option local_context := none) : type_context expr
/-- Iterate over all mvars in the mvar context. -/
meta constant fold_mvars {α : Type} (f : α → expr → type_context α) : α → type_context α
meta def list_mvars : type_context (list expr) := fold_mvars (λ l x, pure $ x :: l) []
/-- Set the mvar to the following assignments.
Works for temporary metas too.
[WARNING] `assign` does not perform certain checks:
- No typecheck is done before assignment.
- If the metavariable is already assigned this will clobber the assignment.
- It will not stop you from assigning an metavariable to itself or creating cycles of metavariable assignments.
  These will manifest as 'deep recursion' exceptions when `instantiate_mvars` is used.
- It is not checked whether the assignment uses local constants outside the declaration's context.

You can avoid the unsafety by using `unify` instead.
-/
meta constant assign (mvar : expr) (assignment : expr) : type_context unit
/-- Assigns a given level metavariable. -/
meta constant level.assign (mvar : level) (assignment : level) : type_context unit
/-- Returns true if the given expression is a declared local constant or a declared metavariable. -/
meta constant is_declared (e : expr) : type_context bool
meta constant is_assigned (mvar : expr) : type_context bool
/-- Given a metavariable, returns the local context that the metavariable was declared with. -/
meta constant get_context (mvar : expr) : type_context local_context
/-- Get the expression that is assigned to the given mvar expression. Fails if given a -/
meta constant get_assignment (mvar : expr) : type_context expr

meta constant instantiate_mvars : expr → type_context expr
meta constant level.instantiate_mvars : level → type_context level

meta constant is_tmp_mvar (mvar : expr) : type_context bool
meta constant is_regular_mvar (mvar : expr) : type_context bool

/-- Run the given `type_context` monad in a temporary mvar scope.
Doing this twice will push the old tmp_mvar assignments to a stack.
So it is safe to do this whether or not you are already in tmp mode. -/
meta constant tmp_mode (n_uvars n_mvars : nat) : type_context α → type_context α

/-- Returns true when in temp mode. -/
meta constant in_tmp_mode : type_context bool
meta constant tmp_is_assigned : nat → type_context bool
meta constant tmp_get_assignment : nat → type_context expr

meta constant level.tmp_is_assigned : nat → type_context bool
meta constant level.tmp_get_assignment : nat → type_context level

/-- Replace each metavariable in the given expression with a temporary metavariable. -/
meta constant to_tmp_mvars : expr → type_context (expr × list level × list expr)
meta constant mk_tmp_mvar (index : nat) (type : expr): expr
meta constant level.mk_tmp_mvar (index : nat) : level
/-- Return tt iff `t` "occurs" in `e`. The occurrence checking is performed using
    keyed matching with the given transparency setting.

    We say `t` occurs in `e` by keyed matching iff there is a subterm `s`
    s.t. `t` and `s` have the same head, and `is_def_eq t s md`

    The main idea is to minimize the number of `is_def_eq` checks
    performed. -/
meta constant kdepends_on (e t : expr) : type_context bool
/-- Abstracts all occurrences of the term `t` in `e` using keyed matching.
    If `unify` is `ff`, then matching is used instead of unification.
    That is, metavariables occurring in `e` are not assigned. -/
meta constant kabstract (e t : expr) (unify := tt) : type_context expr

/-- Run the provided type_context within a backtracking scope.
This means that any changes to the metavariable context will not be committed if the inner monad fails.
[warning]: the local context modified by `push_local` and `pop_local` is not affected by `try`.
Any unpopped locals will be present after the `try` even if the inner `type_context` failed.
-/
meta constant try {α : Type} : type_context α → type_context (option α)

meta def orelse {α : Type} : type_context α → type_context α → type_context α
| x y := try x >>= λ x, option.rec y pure x

meta instance type_context_alternative : alternative type_context := {
    failure := λ α, type_context.fail "failed",
    orelse := λ α x y, type_context.orelse x y
}

/-- Runs the given type_context monad using the type context of the current tactic state.
You can use this to perform unsafe operations such as direct metavariable assignment and the use of temporary metavariables.
-/
meta constant run (inner : type_context α) (tr := tactic.transparency.semireducible) : tactic α

meta def trace {α} [has_to_format α] : α → type_context unit | a :=
   pure $ _root_.trace_fmt (to_fmt a) (λ u, ())

meta def print_mvars : type_context unit := do
    mvs ← list_mvars,
    mvs ← pure $ mvs.map (λ x, match x with (expr.mvar _ pp _) := to_fmt pp | _ := "" end),
    trace mvs

/-- Same as tactic.get_fun_info -/
meta constant get_fun_info (f : expr) (nargs : option nat := none) : type_context fun_info

end type_context
end tactic.unsafe
