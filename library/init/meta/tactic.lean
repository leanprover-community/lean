/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.function init.data.option.basic init.util
import init.control.combinators init.control.monad init.control.alternative init.control.monad_fail
import init.data.nat.div init.meta.exceptional init.meta.format init.meta.environment
import init.meta.pexpr init.data.repr init.data.string.basic init.meta.interaction_monad
import init.classical

open native

meta constant tactic_state : Type

universes u v

namespace tactic_state
meta constant env         : tactic_state → environment
/-- Format the given tactic state. If `target_lhs_only` is true and the target
    is of the form `lhs ~ rhs`, where `~` is a simplification relation,
    then only the `lhs` is displayed.

    Remark: the parameter `target_lhs_only` is a temporary hack used to implement
    the `conv` monad. It will be removed in the future. -/
meta constant to_format   (s : tactic_state) (target_lhs_only : bool := ff) : format
/-- Format expression with respect to the main goal in the tactic state.
   If the tactic state does not contain any goals, then format expression
   using an empty local context. -/
meta constant format_expr : tactic_state → expr → format
meta constant get_options : tactic_state → options
meta constant set_options : tactic_state → options → tactic_state
end tactic_state

meta instance : has_to_format tactic_state :=
⟨tactic_state.to_format⟩

meta instance : has_to_string tactic_state :=
⟨λ s, (to_fmt s).to_string s.get_options⟩

/-- `tactic` is the monad for building tactics.
    You use this to:
    - View and modify the local goals and hypotheses in the prover's state.
    - Invoke type checking and elaboration of terms.
    - View and modify the environment.
    - Build new tactics out of existing ones such as `simp` and `rewrite`.
-/
@[reducible] meta def tactic := interaction_monad tactic_state
@[reducible] meta def tactic_result := interaction_monad.result tactic_state

namespace tactic
  export interaction_monad (result result.success result.exception result.cases_on
    result_to_string mk_exception silent_fail orelse' bracket)
  /-- Cause the tactic to fail with no error message. -/
  meta def failed {α : Type} : tactic α := interaction_monad.failed
  meta def fail {α : Type u} {β : Type v} [has_to_format β] (msg : β) : tactic α :=
  interaction_monad.fail msg
end tactic

namespace tactic_result
  export interaction_monad.result
end tactic_result

open tactic
open tactic_result

infixl ` >>=[tactic] `:2 := interaction_monad_bind
infixl ` >>[tactic] `:2  := interaction_monad_seq

meta instance : alternative tactic :=
{ failure := @interaction_monad.failed _,
  orelse  := @interaction_monad_orelse _,
  ..interaction_monad.monad }

meta def {u₁ u₂} tactic.up {α : Type u₂} (t : tactic α) : tactic (ulift.{u₁} α) :=
λ s, match t s with
| success a s'      := success (ulift.up a) s'
| exception t ref s := exception t ref s
end

meta def {u₁ u₂} tactic.down {α : Type u₂} (t : tactic (ulift.{u₁} α)) : tactic α :=
λ s, match t s with
| success (ulift.up a) s' := success a s'
| exception t ref s       := exception t ref s
end

namespace interactive

/-- Typeclass for custom interaction monads, which provides
    the information required to convert an interactive-mode
    construction to a `tactic` which can actually be executed.

    Given a `[monad m]`, `execute_with` explains how to turn a `begin ... end`
    block, or a `by ...` statement into a `tactic α` which can actually be
    executed. The `inhabited` first argument facilitates the passing of an
    optional configuration parameter `config`, using the syntax:
    ```
    begin [custom_monad] with config,
        ...
    end
    ```
-/
meta class executor (m : Type → Type u) [monad m] :=
(config_type : Type)
[inhabited : inhabited config_type]
(execute_with : config_type → m unit → tactic unit)

attribute [inline] executor.execute_with

@[inline]
meta def executor.execute_explicit (m : Type → Type u)
   [monad m] [e : executor m] : m unit → tactic unit :=
executor.execute_with e.inhabited.default

@[inline]
meta def executor.execute_with_explicit (m : Type → Type u)
   [monad m] [executor m] : executor.config_type m → m unit → tactic unit :=
executor.execute_with

/-- Default `executor` instance for `tactic`s themselves -/
meta instance executor_tactic : executor tactic :=
{ config_type := unit,
  inhabited := ⟨()⟩,
  execute_with := λ _, id }

end interactive

namespace tactic

open interaction_monad.result

variables {α : Type u}

/-- Does nothing. -/
meta def skip : tactic unit :=
success ()

/--
`try_core t` acts like `t`, but succeeds even if `t` fails. It returns the
result of `t` if `t` succeeded and `none` otherwise.
-/
meta def try_core (t : tactic α) : tactic (option α) := λ s,
match t s with
| (exception _ _ _) := success none s
| (success a s') := success (some a) s'
end

/--
`try t` acts like `t`, but succeeds even if `t` fails.
-/
meta def try (t : tactic α) : tactic unit := λ s,
match t s with
| (exception _ _ _) := success () s
| (success _ s') := success () s'
end

meta def try_lst : list (tactic unit) → tactic unit
| []            := failed
| (tac :: tacs) := λ s,
  match tac s with
  | success _ s' := try (try_lst tacs) s'
  | exception e p s' :=
    match try_lst tacs s' with
    | exception _ _ _ := exception e p s'
    | r := r
    end
  end

/--
`fail_if_success t` acts like `t`, but succeeds if `t` fails and fails if `t`
succeeds. Changes made by `t` to the `tactic_state` are preserved only if `t`
succeeds.
-/
meta def fail_if_success {α : Type u} (t : tactic α) : tactic unit := λ s,
match (t s) with
| (success a s) := mk_exception "fail_if_success combinator failed, given tactic succeeded" none s
| (exception _ _ _) := success () s
end

/--
`success_if_fail t` acts like `t`, but succeeds if `t` fails and fails if `t`
succeeds. Changes made by `t` to the `tactic_state` are preserved only if `t`
succeeds.
-/
meta def success_if_fail {α : Type u} (t : tactic α) : tactic unit := λ s,
match t s with
| (success a s) :=
   mk_exception "success_if_fail combinator failed, given tactic succeeded" none s
| (exception _ _ _) := success () s
end

open nat

/--
`iterate_at_most n t` iterates `t` `n` times or until `t` fails, returning the
result of each successful iteration.
-/
meta def iterate_at_most : nat → tactic α → tactic (list α)
| 0       t := pure []
| (n + 1) t := do
  (some a) ← try_core t | pure [],
  as ← iterate_at_most n t,
  pure $ a :: as

/--
`iterate_at_most' n t` repeats `t` `n` times or until `t` fails.
-/
meta def iterate_at_most' : nat → tactic unit → tactic unit
| 0        t := skip
| (succ n) t := do
  (some _) ← try_core t | skip,
  iterate_at_most' n t

/--
`iterate_exactly n t` iterates `t` `n` times, returning the result of
each iteration. If any iteration fails, the whole tactic fails.
-/
meta def iterate_exactly : nat → tactic α → tactic (list α)
| 0       t := pure []
| (n + 1) t := do
  a ← t,
  as ← iterate_exactly n t,
  pure $ a ::as

/--
`iterate_exactly' n t` executes `t` `n` times. If any iteration fails, the whole
tactic fails.
-/
meta def iterate_exactly' : nat → tactic unit → tactic unit
| 0       t := skip
| (n + 1) t := t *> iterate_exactly' n t

/--
`iterate t` repeats `t` 100.000 times or until `t` fails, returning the
result of each iteration.
-/
meta def iterate : tactic α → tactic (list α) :=
iterate_at_most 100000

/--
`iterate' t` repeats `t` 100.000 times or until `t` fails.
-/
meta def iterate' : tactic unit → tactic unit :=
iterate_at_most' 100000

meta def returnopt (e : option α) : tactic α :=
λ s, match e with
| (some a) := success a s
| none     := mk_exception "failed" none s
end

meta instance opt_to_tac : has_coe (option α) (tactic α) :=
⟨returnopt⟩

/-- Decorate t's exceptions with msg. -/
meta def decorate_ex (msg : format) (t : tactic α) : tactic α :=
λ s, result.cases_on (t s)
  success
  (λ opt_thunk,
     match opt_thunk with
     | some e := exception (some (λ u, msg ++ format.nest 2 (format.line ++ e u)))
     | none   := exception none
     end)

/-- Set the tactic_state. -/
@[inline] meta def write (s' : tactic_state) : tactic unit :=
λ s, success () s'

/-- Get the tactic_state. -/
@[inline] meta def read : tactic tactic_state :=
λ s, success s s

/--
`capture t` acts like `t`, but succeeds with a result containing either the returned value
or the exception.
Changes made by `t` to the `tactic_state` are preserved in both cases.

The result can be used to inspect the error message, or passed to `unwrap` to rethrow the
failure later.
-/
meta def capture (t : tactic α) : tactic (tactic_result α) :=
λ s, match t s with
| (success r s') := success (success r s') s'
| (exception f p s') := success (exception f p s') s'
end

/--
`unwrap r` unwraps a result previously obtained using `capture`.

If the previous result was a success, this produces its wrapped value.
If the previous result was an exception, this "rethrows" the exception as if it came
from where it originated.

`do r ← capture t, unwrap r` is identical to `t`, but allows for intermediate tactics to be inserted.
-/
meta def unwrap {α : Type*} (t : tactic_result α) : tactic α :=
match t with
| (success r s') := return r
| e := λ s, e
end

/--
`resume r` continues execution from a result previously obtained using `capture`.

This is like `unwrap`, but the `tactic_state` is rolled back to point of capture even upon success.
-/
meta def resume {α : Type*} (t : tactic_result α) : tactic α :=
λ s, t

meta def get_options : tactic options :=
do s ← read, return s.get_options

meta def set_options (o : options) : tactic unit :=
do s ← read, write (s.set_options o)

meta def save_options {α : Type} (t : tactic α) : tactic α :=
do o ← get_options,
   a ← t,
   set_options o,
   return a

meta def returnex {α : Type} (e : exceptional α) : tactic α :=
λ s, match e with
| exceptional.success a      := success a s
| exceptional.exception f :=
  match get_options s with
  | success opt _   := exception (some (λ u, f opt)) none s
  | exception _ _ _ := exception (some (λ u, f options.mk)) none s
  end
end

meta instance ex_to_tac {α : Type} : has_coe (exceptional α) (tactic α) :=
⟨returnex⟩

end tactic

meta def tactic_format_expr (e : expr) : tactic format :=
do s ← tactic.read, return (tactic_state.format_expr s e)

meta class has_to_tactic_format (α : Type u) :=
(to_tactic_format : α → tactic format)

meta instance : has_to_tactic_format expr :=
⟨tactic_format_expr⟩

meta def tactic.pp {α : Type u} [has_to_tactic_format α] : α → tactic format :=
has_to_tactic_format.to_tactic_format

open tactic format

meta instance {α : Type u} [has_to_tactic_format α] : has_to_tactic_format (list α) :=
⟨λ l, to_fmt <$> l.mmap pp⟩

meta instance (α : Type u) (β : Type v) [has_to_tactic_format α] [has_to_tactic_format β] :
 has_to_tactic_format (α × β) :=
⟨λ ⟨a, b⟩, to_fmt <$> (prod.mk <$> pp a <*> pp b)⟩

meta def option_to_tactic_format {α : Type u} [has_to_tactic_format α] : option α → tactic format
| (some a) := do fa ← pp a, return (to_fmt "(some " ++ fa ++ ")")
| none     := return "none"

meta instance {α : Type u} [has_to_tactic_format α] : has_to_tactic_format (option α) :=
⟨option_to_tactic_format⟩

meta instance {α} (a : α) : has_to_tactic_format (reflected _ a) :=
⟨λ h, pp h.to_expr⟩

@[priority 10] meta instance has_to_format_to_has_to_tactic_format (α : Type) [has_to_format α] : has_to_tactic_format α :=
⟨(λ x, return x) ∘ to_fmt⟩

namespace tactic
open tactic_state

meta def get_env : tactic environment :=
do s ← read,
   return $ env s

meta def get_decl (n : name) : tactic declaration :=
do s ← read,
   (env s).get n

meta constant get_trace_msg_pos : tactic pos

meta def trace {α : Type u} [has_to_tactic_format α] (a : α) : tactic unit :=
do fmt ← pp a,
   return $ _root_.trace_fmt fmt (λ u, ())

meta def trace_call_stack : tactic unit :=
assume state, _root_.trace_call_stack (success () state)

meta def timetac {α : Type u} (desc : string) (t : thunk (tactic α)) : tactic α :=
λ s, timeit desc (t () s)

meta def trace_state : tactic unit :=
do s ← read,
   trace $ to_fmt s

/-- A parameter representing how aggressively definitions should be unfolded when trying to decide if two terms match, unify or are definitionally equal.
By default, theorem declarations are never unfolded.
- `all` will unfold everything, including macros and theorems. Except projection macros.
- `semireducible` will unfold everything except theorems and definitions tagged as irreducible.
- `instances` will unfold all class instance definitions and definitions tagged with reducible.
- `reducible` will only unfold definitions tagged with the `reducible` attribute.
- `none` will never unfold anything.
[NOTE] You are not allowed to tag a definition with more than one of `reducible`, `irreducible`, `semireducible` attributes.
[NOTE] there is a config flag `m_unfold_lemmas`that will make it unfold theorems.
 -/
inductive transparency
| all | semireducible | instances | reducible | none

export transparency (reducible semireducible)

/-- (eval_expr α e) evaluates 'e' IF 'e' has type 'α'. -/
meta constant eval_expr (α : Type u) [reflected _ α] : expr → tactic α

/-- Return the partial term/proof constructed so far. Note that the resultant expression
   may contain variables that are not declarate in the current main goal. -/
meta constant result        : tactic expr
/-- Display the partial term/proof constructed so far. This tactic is *not* equivalent to
   `do { r ← result, s ← read, return (format_expr s r) }` because this one will format the result with respect
   to the current goal, and trace_result will do it with respect to the initial goal. -/
meta constant format_result : tactic format
/-- Return target type of the main goal. Fail if tactic_state does not have any goal left. -/
meta constant target        : tactic expr
meta constant intro_core    : name → tactic expr
meta constant intron        : nat → tactic unit
/-- Clear the given local constant. The tactic fails if the given expression is not a local constant. -/
meta constant clear         : expr → tactic unit
/-- `revert_lst : list expr → tactic nat` is the reverse of `intron`. It takes a local constant `c` and puts it back as bound by a `pi` or `elet` of the main target.
If there are other local constants that depend on `c`, these are also reverted. Because of this, the `nat` that is returned is the actual number of reverted local constants.
Example: with `x : ℕ, h : P(x) ⊢ T(x)`, `revert_lst [x]` returns `2` and produces the state ` ⊢ Π x, P(x) → T(x)`.
 -/
meta constant revert_lst    : list expr → tactic nat
/-- Return `e` in weak head normal form with respect to the given transparency setting.
    If `unfold_ginductive` is `tt`, then nested and/or mutually recursive inductive datatype constructors
    and types are unfolded. Recall that nested and mutually recursive inductive datatype declarations
    are compiled into primitive datatypes accepted by the Kernel. -/
meta constant whnf (e : expr) (md := semireducible) (unfold_ginductive := tt) : tactic expr
/-- (head) eta expand the given expression. `f : α → β` head-eta-expands to `λ a, f a`. If `f` isn't a function then it just returns `f`.  -/
meta constant head_eta_expand : expr → tactic expr
/-- (head) beta reduction. `(λ x, B) c` reduces to `B[x/c]`. -/
meta constant head_beta       : expr → tactic expr
/-- (head) zeta reduction. Reduction of let bindings at the head of the expression. `let x : a := b in c` reduces to `c[x/b]`. -/
meta constant head_zeta       : expr → tactic expr
/-- Zeta reduction. Reduction of let bindings. `let x : a := b in c` reduces to `c[x/b]`. -/
meta constant zeta            : expr → tactic expr
/-- (head) eta reduction. `(λ x, f x)` reduces to `f`. -/
meta constant head_eta        : expr → tactic expr
/-- Succeeds if `t` and `s` can be unified using the given transparency setting. -/
meta constant unify (t s : expr) (md := semireducible) (approx := ff) : tactic unit
/-- Similar to `unify`, but it treats metavariables as constants. -/
meta constant is_def_eq (t s : expr) (md := semireducible) (approx := ff) : tactic unit
/-- Infer the type of the given expression.
   Remark: transparency does not affect type inference -/
meta constant infer_type    : expr → tactic expr

/-- Get the `local_const` expr for the given `name`. -/
meta constant get_local     : name → tactic expr
/-- Resolve a name using the current local context, environment, aliases, etc. -/
meta constant resolve_name  : name → tactic pexpr
/-- Return the hypothesis in the main goal. Fail if tactic_state does not have any goal left. -/
meta constant local_context : tactic (list expr)
/-- Get a fresh name that is guaranteed to not be in use in the local context.
    If `n` is provided and `n` is not in use, then `n` is returned.
    Otherwise a number `i` is appended to give `"n_i"`.
-/
meta constant get_unused_name (n : name := `_x) (i : option nat := none) : tactic name
/--  Helper tactic for creating simple applications where some arguments are inferred using
    type inference.

    Example, given
    ```
        rel.{l_1 l_2} : Pi (α : Type.{l_1}) (β : α -> Type.{l_2}), (Pi x : α, β x) -> (Pi x : α, β x) -> , Prop
        nat     : Type
        real    : Type
        vec.{l} : Pi (α : Type l) (n : nat), Type.{l1}
        f g     : Pi (n : nat), vec real n
    ```
    then
    ```
    mk_app_core semireducible "rel" [f, g]
    ```
    returns the application
    ```
    rel.{1 2} nat (fun n : nat, vec real n) f g
    ```

    The unification constraints due to type inference are solved using the transparency `md`.
-/
meta constant mk_app (fn : name) (args : list expr) (md := semireducible) : tactic expr
/-- Similar to `mk_app`, but allows to specify which arguments are explicit/implicit.
   Example, given `(a b : nat)` then
   ```
   mk_mapp "ite" [some (a > b), none, none, some a, some b]
   ```
   returns the application
   ```
   @ite.{1} nat (a > b) (nat.decidable_gt a b) a b
   ```
-/
meta constant mk_mapp (fn : name) (args : list (option expr)) (md := semireducible) : tactic expr
/-- (mk_congr_arg h₁ h₂) is a more efficient version of (mk_app `congr_arg [h₁, h₂]) -/
meta constant mk_congr_arg  : expr → expr → tactic expr
/-- (mk_congr_fun h₁ h₂) is a more efficient version of (mk_app `congr_fun [h₁, h₂]) -/
meta constant mk_congr_fun  : expr → expr → tactic expr
/-- (mk_congr h₁ h₂) is a more efficient version of (mk_app `congr [h₁, h₂]) -/
meta constant mk_congr      : expr → expr → tactic expr
/-- (mk_eq_refl h) is a more efficient version of (mk_app `eq.refl [h]) -/
meta constant mk_eq_refl    : expr → tactic expr
/-- (mk_eq_symm h) is a more efficient version of (mk_app `eq.symm [h]) -/
meta constant mk_eq_symm    : expr → tactic expr
/-- (mk_eq_trans h₁ h₂) is a more efficient version of (mk_app `eq.trans [h₁, h₂]) -/
meta constant mk_eq_trans   : expr → expr → tactic expr
/-- (mk_eq_mp h₁ h₂) is a more efficient version of (mk_app `eq.mp [h₁, h₂]) -/
meta constant mk_eq_mp      : expr → expr → tactic expr
/-- (mk_eq_mpr h₁ h₂) is a more efficient version of (mk_app `eq.mpr [h₁, h₂]) -/
meta constant mk_eq_mpr      : expr → expr → tactic expr
/-- Given a local constant t, if t has type (lhs = rhs) apply substitution.
   Otherwise, try to find a local constant that has type of the form (t = t') or (t' = t).
   The tactic fails if the given expression is not a local constant. -/
meta constant subst_core     : expr → tactic unit
/-- Close the current goal using `e`. Fail if the type of `e` is not definitionally equal to
    the target type. -/
meta constant exact (e : expr) (md := semireducible) : tactic unit
/-- Elaborate the given quoted expression with respect to the current main goal.
    Note that this means that any implicit arguments for the given `pexpr` will be applied with fresh metavariables.
    If `allow_mvars` is tt, then metavariables are tolerated and become new goals if `subgoals` is tt. -/
meta constant to_expr (q : pexpr) (allow_mvars := tt) (subgoals := tt) : tactic expr
/-- Return true if the given expression is a type class. -/
meta constant is_class      : expr → tactic bool
/-- Try to create an instance of the given type class. -/
meta constant mk_instance   : expr → tactic expr
/-- Change the target of the main goal.
   The input expression must be definitionally equal to the current target.
   If `check` is `ff`, then the tactic does not check whether `e`
   is definitionally equal to the current target. If it is not,
   then the error will only be detected by the kernel type checker. -/
meta constant change (e : expr) (check : bool := tt): tactic unit
/-- `assert_core H T`, adds a new goal for T, and change target to `T -> target`. -/
meta constant assert_core   : name → expr → tactic unit
/-- `assertv_core H T P`, change target to (T -> target) if P has type T. -/
meta constant assertv_core  : name → expr → expr → tactic unit
/-- `define_core H T`, adds a new goal for T, and change target to  `let H : T := ?M in target` in the current goal. -/
meta constant define_core   : name → expr → tactic unit
/-- `definev_core H T P`, change target to `let H : T := P in target` if P has type T. -/
meta constant definev_core  : name → expr → expr → tactic unit
/-- Rotate goals to the left. That is, `rotate_left 1` takes the main goal and puts it to the back of the subgoal list. -/
meta constant rotate_left   : nat → tactic unit
/-- Gets a list of metavariables, one for each goal. -/
meta constant get_goals     : tactic (list expr)
/-- Replace the current list of goals with the given one. Each expr in the list should be a metavariable. Any assigned metavariables will be ignored.-/
meta constant set_goals     : list expr → tactic unit
/-- Convenience function for creating ` for proofs. -/
meta def mk_tagged_proof (prop : expr) (pr : expr) (tag : name) : expr :=
expr.mk_app (expr.const ``id_tag []) [expr.const tag [], prop, pr]

/-- How to order the new goals made from an `apply` tactic.
Supposing we were applying `e : ∀ (a:α) (p : P(a)), Q`
- `non_dep_first` would produce goals `⊢ P(?m)`, `⊢ α`. It puts the P goal at the front because none of the arguments after `p` in `e` depend on `p`. It doesn't matter what the result `Q` depends on.
- `non_dep_only` would produce goal `⊢ P(?m)`.
- `all` would produce goals `⊢ α`, `⊢ P(?m)`.
-/
inductive new_goals
| non_dep_first | non_dep_only | all
/-- Configuration options for the `apply` tactic.
- `md` sets how aggressively definitions are unfolded.
- `new_goals` is the strategy for ordering new goals.
- `instances` if `tt`, then `apply` tries to synthesize unresolved `[...]` arguments using type class resolution.
- `auto_param` if `tt`, then `apply` tries to synthesize unresolved `(h : p . tac_id)` arguments using tactic `tac_id`.
- `opt_param` if `tt`, then `apply` tries to synthesize unresolved `(a : t := v)` arguments by setting them to `v`.
- `unify` if `tt`, then `apply` is free to assign existing metavariables in the goal when solving unification constraints.
   For example, in the goal `|- ?x < succ 0`, the tactic `apply succ_lt_succ` succeeds with the default configuration,
   but `apply_with succ_lt_succ {unify := ff}` doesn't since it would require Lean to assign `?x` to `succ ?y` where
   `?y` is a fresh metavariable.
-/
structure apply_cfg :=
(md            := semireducible)
(approx        := tt)
(new_goals     := new_goals.non_dep_first)
(instances     := tt)
(auto_param    := tt)
(opt_param     := tt)
(unify         := tt)
/-- Apply the expression `e` to the main goal, the unification is performed using the transparency mode in `cfg`.
    Supposing `e : Π (a₁:α₁) ... (aₙ:αₙ), P(a₁,...,aₙ)` and the target is `Q`, `apply` will attempt to unify `Q` with `P(?a₁,...?aₙ)`.
    All of the metavariables that are not assigned are added as new metavariables.
    If `cfg.approx` is `tt`, then fallback to first-order unification, and approximate context during unification.
    `cfg.new_goals` specifies which unassigned metavariables become new goals, and their order.
    If `cfg.instances` is `tt`, then use type class resolution to instantiate unassigned meta-variables.
    The fields `cfg.auto_param` and `cfg.opt_param` are ignored by this tactic (See `tactic.apply`).
    It returns a list of all introduced meta variables and the parameter name associated with them, even the assigned ones. -/
meta constant apply_core (e : expr) (cfg : apply_cfg := {}) : tactic (list (name × expr))
/-- Create a fresh meta universe variable. -/
meta constant mk_meta_univ  : tactic level
/-- Create a fresh meta-variable with the given type.
   The scope of the new meta-variable is the local context of the main goal. -/
meta constant mk_meta_var   : expr → tactic expr
/-- Return the value assigned to the given universe meta-variable.
   Fail if argument is not an universe meta-variable or if it is not assigned. -/
meta constant get_univ_assignment : level → tactic level
/-- Return the value assigned to the given meta-variable.
   Fail if argument is not a meta-variable or if it is not assigned. -/
meta constant get_assignment : expr → tactic expr
/-- Return true if the given meta-variable is assigned.
    Fail if argument is not a meta-variable. -/
meta constant is_assigned : expr → tactic bool
/-- Make a name that is guaranteed to be unique. Eg `_fresh.1001.4667`. These will be different for each run of the tactic.  -/
meta constant mk_fresh_name : tactic name

/-- Induction on `h` using recursor `rec`, names for the new hypotheses
   are retrieved from `ns`. If `ns` does not have sufficient names, then use the internal binder names
   in the recursor.
   It returns for each new goal the name of the constructor (if `rec_name` is a builtin recursor),
   a list of new hypotheses, and a list of substitutions for hypotheses
   depending on `h`. The substitutions map internal names to their replacement terms. If the
   replacement is again a hypothesis the user name stays the same. The internal names are only valid
   in the original goal, not in the type context of the new goal.
   Remark: if `rec_name` is not a builtin recursor, we use parameter names of `rec_name` instead of
   constructor names.

   If `rec` is none, then the type of `h` is inferred, if it is of the form `C ...`, tactic uses `C.rec` -/
meta constant induction (h : expr) (ns : list name := []) (rec : option name := none) (md := semireducible) : tactic (list (name × list expr × list (name × expr)))
/-- Apply `cases_on` recursor, names for the new hypotheses are retrieved from `ns`.
   `h` must be a local constant. It returns for each new goal the name of the constructor, a list of new hypotheses, and a list of
   substitutions for hypotheses depending on `h`. The number of new goals may be smaller than the
   number of constructors. Some goals may be discarded when the indices to not match.
   See `induction` for information on the list of substitutions.

   The `cases` tactic is implemented using this one, and it relaxes the restriction of `h`.

   Note: There is one "new hypothesis" for every constructor argument. These are
   usually local constants, but due to dependent pattern matching, they can also
   be arbitrary terms. -/
meta constant cases_core (h : expr) (ns : list name := []) (md := semireducible) : tactic (list (name × list expr × list (name × expr)))
/-- Similar to cases tactic, but does not revert/intro/clear hypotheses. -/
meta constant destruct (e : expr) (md := semireducible) : tactic unit
/-- Generalizes the target with respect to `e`.  -/
meta constant generalize (e : expr) (n : name := `_x) (md := semireducible) : tactic unit
/-- instantiate assigned metavariables in the given expression -/
meta constant instantiate_mvars : expr → tactic expr
/-- Add the given declaration to the environment -/
meta constant add_decl : declaration → tactic unit
/--
Changes the environment to the `new_env`.
The new environment does not need to be a descendant of the old one.
Use with care.
-/
meta constant set_env_core : environment → tactic unit
/-- Changes the environment to the `new_env`. `new_env` needs to be a descendant from the current environment. -/
meta constant set_env : environment → tactic unit
/-- `doc_string env d k` returns the doc string for `d` (if available) -/
meta constant doc_string : name → tactic string
/-- Set the docstring for the given declaration. -/
meta constant add_doc_string : name → string → tactic unit
/--
Create an auxiliary definition with name `c` where `type` and `value` may contain local constants and
meta-variables. This function collects all dependencies (universe parameters, universe metavariables,
local constants (aka hypotheses) and metavariables).
It updates the environment in the tactic_state, and returns an expression of the form

          (c.{l_1 ... l_n} a_1 ... a_m)

where l_i's and a_j's are the collected dependencies.
-/
meta constant add_aux_decl (c : name) (type : expr) (val : expr) (is_lemma : bool) : tactic expr

/-- Returns a list of all top-level (`/-! ... -/`) docstrings in the active module and imported ones.
The returned object is a list of modules, indexed by `(some filename)` for imported modules
and `none` for the active one, where each module in the list is paired with a list
of `(position_in_file, docstring)` pairs. -/
meta constant olean_doc_strings : tactic (list (option string × (list (pos × string))))

/-- Returns a list of docstrings in the active module. An entry in the list can be either:
- a top-level (`/-! ... -/`) docstring, represented as `(none, docstring)`
- a declaration-specific (`/-- ... -/`) docstring, represented as `(some decl_name, docstring)` -/
meta def module_doc_strings : tactic (list (option name × string)) :=
  do
    /- Obtain a list of top-level docs in current module. -/
    mod_docs ← olean_doc_strings,
    let mod_docs: list (list (option name × string)) :=
      mod_docs.filter_map (λ d,
        if d.1.is_none
          then some (d.2.map
            (λ pos_doc, ⟨none, pos_doc.2⟩))
          else none),
    let mod_docs := mod_docs.join,
    /- Obtain list of declarations in current module. -/
    e ← get_env,
    let decls := environment.fold e ([]: list name)
      (λ d acc, let n := d.to_name in
      if (environment.decl_olean e n).is_none
        then n::acc else acc),
    /- Map declarations to those which have docstrings. -/
    decls ← decls.mfoldl (λa n,
      (doc_string n >>=
        λ doc, pure $ (some n, doc) :: a)
      <|> pure a) [],
    pure (mod_docs ++ decls)

/-- Set attribute `attr_name` for constant `c_name` with the given priority.
   If the priority is none, then use default -/
meta constant set_basic_attribute (attr_name : name) (c_name : name) (persistent := ff) (prio : option nat := none) : tactic unit
/-- `unset_attribute attr_name c_name` -/
meta constant unset_attribute : name → name → tactic unit
/-- `has_attribute attr_name c_name` succeeds if the declaration `decl_name`
   has the attribute `attr_name`. The result is the priority and whether or not
   the attribute is persistent. -/
meta constant has_attribute : name → name → tactic (bool × nat)

/-- `copy_attribute attr_name c_name p d_name` copy attribute `attr_name` from
   `src` to `tgt` if it is defined for `src`; make it persistent if `p` is `tt`;
   if `p` is `none`, the copied attribute is made persistent iff it is persistent on `src`  -/
meta def copy_attribute (attr_name : name) (src : name) (tgt : name) (p : option bool := none) : tactic unit :=
try $ do
  (p', prio) ← has_attribute attr_name src,
  let p := p.get_or_else p',
  set_basic_attribute attr_name tgt p (some prio)

/-- Name of the declaration currently being elaborated. -/
meta constant decl_name : tactic name

/-- `save_type_info e ref` save (typeof e) at position associated with ref -/
meta constant save_type_info {elab : bool} : expr → expr elab → tactic unit
meta constant save_info_thunk : pos → (unit → format) → tactic unit
/-- Return list of currently open namespaces -/
meta constant open_namespaces : tactic (list name)
/-- Return tt iff `t` "occurs" in `e`. The occurrence checking is performed using
    keyed matching with the given transparency setting.

    We say `t` occurs in `e` by keyed matching iff there is a subterm `s`
    s.t. `t` and `s` have the same head, and `is_def_eq t s md`

    The main idea is to minimize the number of `is_def_eq` checks
    performed. -/
meta constant kdepends_on (e t : expr) (md := reducible) : tactic bool
/-- Abstracts all occurrences of the term `t` in `e` using keyed matching.
    If `unify` is `ff`, then matching is used instead of unification.
    That is, metavariables occurring in `e` are not assigned. -/
meta constant kabstract (e t : expr) (md := reducible) (unify := tt) : tactic expr

/-- Blocks the execution of the current thread for at least `msecs` milliseconds.
    This tactic is used mainly for debugging purposes. -/
meta constant sleep (msecs : nat) : tactic unit

/-- Type check `e` with respect to the current goal.
    Fails if `e` is not type correct. -/
meta constant type_check (e : expr) (md := semireducible) : tactic unit
open list nat

/-- A `tag` is a list of `names`. These are attached to goals to help tactics track them.-/
def tag : Type := list name

/-- Enable/disable goal tagging.  -/
meta constant enable_tags (b : bool) : tactic unit
/-- Return tt iff goal tagging is enabled. -/
meta constant tags_enabled : tactic bool
/-- Tag goal `g` with tag `t`. It does nothing if goal tagging is disabled.
    Remark: `set_goal g []` removes the tag -/
meta constant set_tag (g : expr) (t : tag) : tactic unit
/-- Return tag associated with `g`. Return `[]` if there is no tag. -/
meta constant get_tag (g : expr) : tactic tag

/-! By default, Lean only considers local instances in the header of declarations.
    This has two main benefits.
    1- Results produced by the type class resolution procedure can be easily cached.
    2- The set of local instances does not have to be recomputed.

    This approach has the following disadvantages:
    1- Frozen local instances cannot be reverted.
    2- Local instances defined inside of a declaration are not considered during type
       class resolution.
-/

/--
Avoid this function!  Use `unfreezingI`/`resetI`/etc. instead!

Unfreezes the current set of local instances.
After this tactic, the instance cache is disabled.
-/
meta constant unfreeze_local_instances : tactic unit
/--
Freeze the current set of local instances.
-/
meta constant freeze_local_instances : tactic unit
/-- Return the list of frozen local instances. Return `none` if local instances were not frozen. -/
meta constant frozen_local_instances : tactic (option (list expr))

/-- Run the provided tactic, associating it to the given AST node. -/
meta constant with_ast {α : Type u} (ast : ℕ) (t : tactic α) : tactic α

meta def induction' (h : expr) (ns : list name := []) (rec : option name := none) (md := semireducible) : tactic unit :=
induction h ns rec md >> return ()

/-- Remark: set_goals will erase any solved goal -/
meta def cleanup : tactic unit :=
get_goals >>= set_goals

/-- Auxiliary definition used to implement begin ... end blocks -/
meta def step {α : Type u} (t : tactic α) : tactic unit :=
t >>[tactic] cleanup

meta def istep {α : Type u} (line0 col0 line col ast : ℕ) (t : tactic α) : tactic unit :=
λ s, (@scope_trace _ line col (λ _, with_ast ast (step t) s)).clamp_pos line0 line col

meta def is_prop (e : expr) : tactic bool :=
do t ← infer_type e,
   return (t = `(Prop))

/-- Return true iff n is the name of declaration that is a proposition. -/
meta def is_prop_decl (n : name) : tactic bool :=
do env ← get_env,
   d   ← env.get n,
   t   ← return $ d.type,
   is_prop t

meta def is_proof (e : expr) : tactic bool :=
infer_type e >>= is_prop

meta def whnf_no_delta (e : expr) : tactic expr :=
whnf e transparency.none

/-- Return `e` in weak head normal form with respect to the given transparency setting,
    or `e` head is a generalized constructor or inductive datatype. -/
meta def whnf_ginductive (e : expr) (md := semireducible) : tactic expr :=
whnf e md ff

meta def whnf_target : tactic unit :=
target >>= whnf >>= change
/-- Change the target of the main goal.
   The input expression must be definitionally equal to the current target.
   The tactic does not check whether `e`
   is definitionally equal to the current target. The error will only be detected by the kernel type checker. -/
meta def unsafe_change (e : expr) : tactic unit :=
change e ff

/-- Pi or elet introduction.
Given the tactic state `⊢ Π x : α, Y`, ``intro `hello`` will produce the state `hello : α ⊢ Y[x/hello]`.
Returns the new local constant. Similarly for `elet` expressions.
If the target is not a Pi or elet it will try to put it in WHNF.
 -/
meta def intro (n : name) : tactic expr :=
do t ← target,
   if expr.is_pi t ∨ expr.is_let t then intro_core n
   else whnf_target >> intro_core n

/--
A variant of `intro` which makes sure that the introduced hypothesis's name is
unique in the context. If there is no hypothesis named `n` in the context yet,
`intro_fresh n` is the same as `intro n`. If there is already a hypothesis named
`n`, the new hypothesis is named `n_1` (or `n_2` if `n_1` already exists, etc.).
If `offset` is given, the new names are `n_offset`, `n_offset+1` etc.

If `n` is `_`, `intro_fresh n` is the same as `intro1`. The `offset` is ignored
in this case.
-/
meta def intro_fresh (n : name) (offset : option nat := none) : tactic expr :=
  if n = `_
    then intro `_
    else do
      n ← get_unused_name n offset,
      intro n

/-- Like `intro` except the name is derived from the bound name in the Π. -/
meta def intro1 : tactic expr :=
intro `_

/-- Repeatedly apply `intro1` and return the list of new local constants in order of introduction. -/
meta def intros : tactic (list expr) :=
do t ← target,
match t with
| expr.pi   _ _ _ _ := do H ← intro1, Hs ← intros, return (H :: Hs)
| expr.elet _ _ _ _ := do H ← intro1, Hs ← intros, return (H :: Hs)
| _                 := return []
end

/-- Same as `intros`, except with the given names for the new hypotheses. Use the name ```_``` to instead use the binder's name.-/
meta def intro_lst (ns : list name) : tactic (list expr) :=
ns.mmap intro

/--
A variant of `intro_lst` which makes sure that the introduced hypotheses' names
are unique in the context. See `intro_fresh`.
-/
meta def intro_lst_fresh (ns : list name) : tactic (list expr) :=
ns.mmap intro_fresh

/-- Introduces new hypotheses with forward dependencies.  -/
meta def intros_dep : tactic (list expr) :=
do t ← target,
   let proc (b : expr) :=
      if b.has_var_idx 0 then
        do h ← intro1, hs ← intros_dep, return (h::hs)
      else
        -- body doesn't depend on new hypothesis
        return [],
   match t with
   | expr.pi _ _ _ b   := proc b
   | expr.elet _ _ _ b := proc b
   | _                 := return []
   end

meta def introv : list name → tactic (list expr)
| []      := intros_dep
| (n::ns) := do hs ← intros_dep, h ← intro n, hs' ← introv ns, return (hs ++ h :: hs')

/--
`intron' n` introduces `n` hypotheses and returns the resulting local
constants. Fails if there are not at least `n` arguments to introduce. If you do
not need the return value, use `intron`.
-/
meta def intron' (n : ℕ) : tactic (list expr)
:= iterate_exactly n intro1

/--
Like `intron'` but the introduced hypotheses' names are derived from `base`,
i.e. `base`, `base_1` etc. The new names are unique in the context. If `offset`
is given, the new names will be `base_offset`, `base_offset+1` etc.
-/
meta def intron_base (n : ℕ) (base : name) (offset : option nat := none)
  : tactic (list expr)
:= iterate_exactly n (intro_fresh base offset)

/--
`intron_with i ns base offset` introduces `i` hypotheses using the names from
`ns`. If `ns` contains less than `i` names, the remaining hypotheses' names are
derived from `base` and `offset` (as with `intron_base`). If `base` is `_`, the
names are derived from the Π binder names.

Returns the introduced local constants and the remaining names from `ns` (if
`ns` contains more than `i` names).
-/
meta def intron_with
  : ℕ → list name → opt_param name `_ → opt_param (option ℕ) none
  → tactic (list expr × list name)
| 0 ns _ _ := pure ([], ns)
| (i + 1) [] base offset := do
  hs ← intron_base (i + 1) base offset,
  pure (hs, [])
| (i + 1) (n :: ns) base offset := do
  h ← intro n,
  ⟨hs, rest⟩ ← intron_with i ns base offset,
  pure (h :: hs, rest)

/-- Returns n fully qualified if it refers to a constant, or else fails. -/
meta def resolve_constant (n : name) : tactic name :=
do e ← resolve_name n,
   match e with
   | expr.const n _ := pure n
   | _ := do
     e ← to_expr e tt ff,
     expr.const n _ ← pure $ e.get_app_fn,
     pure n
   end

meta def to_expr_strict (q : pexpr) : tactic expr :=
to_expr q

/--
Example: with `x : ℕ, h : P(x) ⊢ T(x)`, `revert x` returns `2` and produces the state ` ⊢ Π x, P(x) → T(x)`.
 -/
meta def revert (l : expr) : tactic nat :=
revert_lst [l]

/-- Revert "all" hypotheses. Actually, the tactic only reverts
   hypotheses occurring after the last frozen local instance.
   Recall that frozen local instances cannot be reverted,
   use `unfreezing revert_all` instead. -/
meta def revert_all : tactic nat :=
do lctx ← local_context,
   lis  ← frozen_local_instances,
   match lis with
   | none           := revert_lst lctx
   | some []        := revert_lst lctx
                       /- `hi` is the last local instance. We shoul truncate `lctx` at `hi`. -/
   | some (hi::his) := revert_lst $ lctx.foldl (λ r h, if h.local_uniq_name = hi.local_uniq_name then [] else h :: r) []
   end

meta def clear_lst : list name → tactic unit
| []      := skip
| (n::ns) := do H ← get_local n, clear H, clear_lst ns

meta def match_not (e : expr) : tactic expr :=
match (expr.is_not e) with
| (some a) := return a
| none     := fail "expression is not a negation"
end

meta def match_and (e : expr) : tactic (expr × expr) :=
match (expr.is_and e) with
| (some (α, β)) := return (α, β)
| none     := fail "expression is not a conjunction"
end

meta def match_or (e : expr) : tactic (expr × expr) :=
match (expr.is_or e) with
| (some (α, β)) := return (α, β)
| none     := fail "expression is not a disjunction"
end

meta def match_iff (e : expr) : tactic (expr × expr) :=
match (expr.is_iff e) with
| (some (lhs, rhs)) := return (lhs, rhs)
| none              := fail "expression is not an iff"
end

meta def match_eq (e : expr) : tactic (expr × expr) :=
match (expr.is_eq e) with
| (some (lhs, rhs)) := return (lhs, rhs)
| none              := fail "expression is not an equality"
end

meta def match_ne (e : expr) : tactic (expr × expr) :=
match (expr.is_ne e) with
| (some (lhs, rhs)) := return (lhs, rhs)
| none              := fail "expression is not a disequality"
end

meta def match_heq (e : expr) : tactic (expr × expr × expr × expr) :=
do match (expr.is_heq e) with
| (some (α, lhs, β, rhs)) := return (α, lhs, β, rhs)
| none                    := fail "expression is not a heterogeneous equality"
end

meta def match_refl_app (e : expr) : tactic (name × expr × expr) :=
do env ← get_env,
match (environment.is_refl_app env e) with
| (some (R, lhs, rhs)) := return (R, lhs, rhs)
| none                 := fail "expression is not an application of a reflexive relation"
end

meta def match_app_of (e : expr) (n : name) : tactic (list expr) :=
guard (expr.is_app_of e n) >> return e.get_app_args

meta def get_local_type (n : name) : tactic expr :=
get_local n >>= infer_type

meta def trace_result : tactic unit :=
format_result >>= trace

meta def rexact (e : expr) : tactic unit :=
exact e reducible

meta def any_hyp_aux {α : Type} (f : expr → tactic α) : list expr → tactic α
| []        := failed
| (h :: hs) := f h <|> any_hyp_aux hs

meta def any_hyp {α : Type} (f : expr → tactic α) : tactic α :=
local_context >>= any_hyp_aux f

/-- `find_same_type t es` tries to find in es an expression with type definitionally equal to t -/
meta def find_same_type : expr → list expr → tactic expr
| e []         := failed
| e (H :: Hs) :=
  do t ← infer_type H,
     (unify e t >> return H) <|> find_same_type e Hs

meta def find_assumption (e : expr) : tactic expr :=
do ctx ← local_context, find_same_type e ctx

meta def assumption : tactic unit :=
do { ctx ← local_context,
     t   ← target,
     H   ← find_same_type t ctx,
     exact H }
<|> fail "assumption tactic failed"

meta def save_info (p : pos) : tactic unit :=
do s ← read,
   tactic.save_info_thunk p (λ _, tactic_state.to_format s)

notation `‹` p `›` := (by assumption : p)

/-- Swap first two goals, do nothing if tactic state does not have at least two goals. -/
meta def swap : tactic unit :=
do gs ← get_goals,
   match gs with
   | (g₁ :: g₂ :: rs) := set_goals (g₂ :: g₁ :: rs)
   | e                := skip
   end

/-- `assert h t`, adds a new goal for t, and the hypothesis `h : t` in the current goal. -/
meta def assert (h : name) (t : expr) : tactic expr :=
do assert_core h t, swap, e ← intro h, swap, return e

/-- `assertv h t v`, adds the hypothesis `h : t` in the current goal if v has type t. -/
meta def assertv (h : name) (t : expr) (v : expr) : tactic expr :=
assertv_core h t v >> intro h

/-- `define h t`, adds a new goal for t, and the hypothesis `h : t := ?M` in the current goal. -/
meta def define  (h : name) (t : expr) : tactic expr :=
do define_core h t, swap, e ← intro h, swap, return e

/-- `definev h t v`, adds the hypothesis (h : t := v) in the current goal if v has type t. -/
meta def definev (h : name) (t : expr) (v : expr) : tactic expr :=
definev_core h t v >> intro h

/-- Add `h : t := pr` to the current goal -/
meta def pose (h : name) (t : option expr := none) (pr : expr) : tactic expr :=
let dv := λt, definev h t pr in
option.cases_on t (infer_type pr >>= dv) dv

/-- Add `h : t` to the current goal, given a proof `pr : t` -/
meta def note (h : name) (t : option expr := none) (pr : expr) : tactic expr :=
let dv := λt, assertv h t pr in
option.cases_on t (infer_type pr >>= dv) dv

/-- Return the number of goals that need to be solved -/
meta def num_goals     : tactic nat :=
do gs ← get_goals,
   return (length gs)

/-- Rotate the goals to the right by `n`. That is, take the goal at the back and push it to the front `n` times.
[NOTE] We have to provide the instance argument `[has_mod nat]` because
   mod for nat was not defined yet -/
meta def rotate_right (n : nat) [has_mod nat] : tactic unit :=
do ng ← num_goals,
   if ng = 0 then skip
   else rotate_left (ng - n % ng)

/-- Rotate the goals to the left by `n`. That is, put the main goal to the back `n` times. -/
meta def rotate : nat → tactic unit :=
rotate_left

private meta def repeat_aux (t : tactic unit) : list expr → list expr → tactic unit
| []      r := set_goals r.reverse
| (g::gs) r := do
  ok ← try_core (set_goals [g] >> t),
  match ok with
  | none := repeat_aux gs (g::r)
  | _    := do
    gs' ← get_goals,
    repeat_aux (gs' ++ gs) r
  end

/-- This tactic is applied to each goal. If the application succeeds,
    the tactic is applied recursively to all the generated subgoals until it eventually fails.
    The recursion stops in a subgoal when the tactic has failed to make progress.
    The tactic `repeat` never fails. -/
meta def repeat (t : tactic unit) : tactic unit :=
do gs ← get_goals, repeat_aux t gs []

/-- `first [t_1, ..., t_n]` applies the first tactic that doesn't fail.
   The tactic fails if all t_i's fail. -/
meta def first {α : Type u} : list (tactic α) → tactic α
| []      := fail "first tactic failed, no more alternatives"
| (t::ts) := t <|> first ts

/-- Applies the given tactic to the main goal and fails if it is not solved. -/
meta def solve1 {α} (tac : tactic α) : tactic α :=
do gs ← get_goals,
   match gs with
   | []      := fail "solve1 tactic failed, there isn't any goal left to focus"
   | (g::rs) :=
     do set_goals [g],
        a ← tac,
        gs' ← get_goals,
        match gs' with
        | [] := set_goals rs >> pure a
        | gs := fail "solve1 tactic failed, focused goal has not been solved"
        end
   end

/-- `solve [t_1, ... t_n]` applies the first tactic that solves the main goal. -/
meta def solve {α} (ts : list (tactic α)) : tactic α :=
first $ map solve1 ts

private meta def focus_aux {α} : list (tactic α) → list expr → list expr → tactic (list α)
| []       []      rs := set_goals rs *> pure []
| (t::ts)  []      rs := fail "focus tactic failed, insufficient number of goals"
| tts      (g::gs) rs :=
  mcond (is_assigned g) (focus_aux tts gs rs) $
    do set_goals [g],
       t::ts ← pure tts | fail "focus tactic failed, insufficient number of tactics",
       a ← t,
       rs' ← get_goals,
       as ← focus_aux ts gs (rs ++ rs'),
       pure $ a :: as

/--
`focus [t_1, ..., t_n]` applies t_i to the i-th goal. Fails if the number of
goals is not n. Returns the results of t_i (one per goal).
-/
meta def focus {α} (ts : list (tactic α)) : tactic (list α) :=
do gs ← get_goals, focus_aux ts gs []

private meta def focus'_aux : list (tactic unit) → list expr → list expr → tactic unit
| []       []      rs := set_goals rs
| (t::ts)  []      rs := fail "focus' tactic failed, insufficient number of goals"
| tts      (g::gs) rs :=
  mcond (is_assigned g) (focus'_aux tts gs rs) $
    do set_goals [g],
       t::ts ← pure tts | fail "focus' tactic failed, insufficient number of tactics",
       t,
       rs' ← get_goals,
       focus'_aux ts gs (rs ++ rs')

/-- `focus' [t_1, ..., t_n]` applies t_i to the i-th goal. Fails if the number of goals is not n. -/
meta def focus' (ts : list (tactic unit)) : tactic unit :=
do gs ← get_goals, focus'_aux ts gs []

meta def focus1 {α} (tac : tactic α) : tactic α :=
do g::gs ← get_goals,
   match gs with
   | [] := tac
   | _  := do
      set_goals [g],
      a ← tac,
      gs' ← get_goals,
      set_goals (gs' ++ gs),
      return a
   end

private meta def all_goals_core {α} (tac : tactic α)
  : list expr → list expr → tactic (list α)
| []        ac := set_goals ac *> pure []
| (g :: gs) ac :=
  mcond (is_assigned g) (all_goals_core gs ac) $
    do set_goals [g],
       a ← tac,
       new_gs ← get_goals,
       as ← all_goals_core gs (ac ++ new_gs),
       pure $ a :: as

/--
Apply the given tactic to all goals. Return one result per goal.
-/
meta def all_goals {α} (tac : tactic α) : tactic (list α) :=
do gs ← get_goals,
   all_goals_core tac gs []

private meta def all_goals'_core (tac : tactic unit) : list expr → list expr → tactic unit
| []        ac := set_goals ac
| (g :: gs) ac :=
  mcond (is_assigned g) (all_goals'_core gs ac) $
    do set_goals [g],
       tac,
       new_gs ← get_goals,
       all_goals'_core gs (ac ++ new_gs)

/-- Apply the given tactic to all goals. -/
meta def all_goals' (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   all_goals'_core tac gs []

private meta def any_goals_core {α} (tac : tactic α) : list expr → list expr → bool → tactic (list (option α))
| []        ac progress := guard progress *> set_goals ac *> pure []
| (g :: gs) ac progress :=
  mcond (is_assigned g) (any_goals_core gs ac progress) $
    do set_goals [g],
       res ← try_core tac,
       new_gs ← get_goals,
       ress ← any_goals_core gs (ac ++ new_gs) (res.is_some || progress),
       pure $ res :: ress

/--
Apply `tac` to any goal where it succeeds. The tactic succeeds if `tac`
succeeds for at least one goal. The returned list contains the result of `tac`
for each goal: `some a` if tac succeeded, or `none` if it did not.
-/
meta def any_goals {α} (tac : tactic α) : tactic (list (option α)) :=
do gs ← get_goals,
   any_goals_core tac gs [] ff

private meta def any_goals'_core (tac : tactic unit) : list expr → list expr → bool → tactic unit
| []        ac progress := guard progress >> set_goals ac
| (g :: gs) ac progress :=
  mcond (is_assigned g) (any_goals'_core gs ac progress) $
    do set_goals [g],
       succeeded ← try_core tac,
       new_gs    ← get_goals,
       any_goals'_core gs (ac ++ new_gs) (succeeded.is_some || progress)

/-- Apply the given tactic to any goal where it succeeds. The tactic succeeds only if
   tac succeeds for at least one goal. -/
meta def any_goals' (tac : tactic unit) : tactic unit :=
do gs ← get_goals,
   any_goals'_core tac gs [] ff

/--
LCF-style AND_THEN tactic. It applies `tac1` to the main goal, then applies
`tac2` to each goal produced by `tac1`.
-/
meta def seq {α β} (tac1 : tactic α) (tac2 : α → tactic β) : tactic (list β) :=
do g::gs ← get_goals,
   set_goals [g],
   a ← tac1,
   bs ← all_goals $ tac2 a,
   gs' ← get_goals,
   set_goals (gs' ++ gs),
   pure bs

/-- LCF-style AND_THEN tactic. It applies tac1, and if succeed applies tac2 to each subgoal produced by tac1 -/
meta def seq' (tac1 : tactic unit) (tac2 : tactic unit) : tactic unit :=
do g::gs ← get_goals,
   set_goals [g],
   tac1, all_goals' tac2,
   gs' ← get_goals,
   set_goals (gs' ++ gs)

/--
Applies `tac1` to the main goal, then applies each of the tactics in `tacs2` to
one of the produced subgoals (like `focus'`).
-/
meta def seq_focus {α β} (tac1 : tactic α) (tacs2 : α → list (tactic β)) : tactic (list β) :=
do g::gs ← get_goals,
   set_goals [g],
   a ← tac1,
   bs ← focus $ tacs2 a,
   gs' ← get_goals,
   set_goals (gs' ++ gs),
   pure bs

/--
Applies `tac1` to the main goal, then applies each of the tactics in `tacs2` to
one of the produced subgoals (like `focus`).
-/
meta def seq_focus' (tac1 : tactic unit) (tacs2 : list (tactic unit)) : tactic unit :=
do g::gs ← get_goals,
   set_goals [g],
   tac1, focus tacs2,
   gs' ← get_goals,
   set_goals (gs' ++ gs)

meta instance andthen_seq : has_andthen (tactic unit) (tactic unit) (tactic unit) :=
⟨seq'⟩

meta instance andthen_seq_focus : has_andthen (tactic unit) (list (tactic unit)) (tactic unit) :=
⟨seq_focus'⟩

meta constant is_trace_enabled_for : name → bool

/-- Execute tac only if option trace.n is set to true. -/
meta def when_tracing (n : name) (tac : tactic unit) : tactic unit :=
when (is_trace_enabled_for n = tt) tac

/-- Fail if there are no remaining goals. -/
meta def fail_if_no_goals : tactic unit :=
do n ← num_goals,
   when (n = 0) (fail "tactic failed, there are no goals to be solved")

/-- Fail if there are unsolved goals. -/
meta def done : tactic unit :=
do n ← num_goals,
   when (n ≠ 0) (fail "done tactic failed, there are unsolved goals")

meta def apply_opt_param : tactic unit :=
do `(opt_param %%t %%v) ← target,
   exact v

meta def apply_auto_param : tactic unit :=
do `(auto_param %%type %%tac_name_expr) ← target,
   change type,
   tac_name ← eval_expr name tac_name_expr,
   tac ← eval_expr (tactic unit) (expr.const tac_name []),
   tac

meta def has_opt_auto_param (ms : list expr) : tactic bool :=
ms.mfoldl
 (λ r m, do type ← infer_type m,
            return $ r || type.is_napp_of `opt_param 2 || type.is_napp_of `auto_param 2)
 ff

meta def try_apply_opt_auto_param (cfg : apply_cfg) (ms : list expr) : tactic unit :=
when (cfg.auto_param || cfg.opt_param) $
mwhen (has_opt_auto_param ms) $ do
  gs ← get_goals,
  ms.mmap' (λ m, mwhen (bnot <$> is_assigned m) $
                   set_goals [m] >>
                   when cfg.opt_param (try apply_opt_param) >>
                   when cfg.auto_param (try apply_auto_param)),
  set_goals gs

meta def has_opt_auto_param_for_apply (ms : list (name × expr)) : tactic bool :=
ms.mfoldl
 (λ r m, do type ← infer_type m.2,
            return $ r || type.is_napp_of `opt_param 2 || type.is_napp_of `auto_param 2)
 ff

meta def try_apply_opt_auto_param_for_apply (cfg : apply_cfg) (ms : list (name × expr)) : tactic unit :=
mwhen (has_opt_auto_param_for_apply ms) $ do
  gs ← get_goals,
  ms.mmap' (λ m, mwhen (bnot <$> (is_assigned m.2)) $
                   set_goals [m.2] >>
                   when cfg.opt_param (try apply_opt_param) >>
                   when cfg.auto_param (try apply_auto_param)),
  set_goals gs

meta def apply (e : expr) (cfg : apply_cfg := {}) : tactic (list (name × expr)) :=
do r ← apply_core e cfg,
   try_apply_opt_auto_param_for_apply cfg r,
   return r

/-- Same as `apply` but __all__ arguments that weren't inferred are added to goal list. -/
meta def fapply (e : expr) : tactic (list (name × expr)) :=
apply e {new_goals := new_goals.all}
/-- Same as `apply` but only goals that don't depend on other goals are added to goal list. -/
meta def eapply (e : expr) : tactic (list (name × expr)) :=
apply e {new_goals := new_goals.non_dep_only}

/-- Try to solve the main goal using type class resolution. -/
meta def apply_instance : tactic unit :=
do tgt ← target >>= instantiate_mvars,
   b   ← is_class tgt,
   if b then mk_instance tgt >>= exact
   else fail "apply_instance tactic fail, target is not a type class"

/-- Create a list of universe meta-variables of the given size. -/
meta def mk_num_meta_univs : nat → tactic (list level)
| 0        := return []
| (succ n) := do
  l  ← mk_meta_univ,
  ls ← mk_num_meta_univs n,
  return (l::ls)

/-- Return `expr.const c [l_1, ..., l_n]` where l_i's are fresh universe meta-variables. -/
meta def mk_const (c : name) : tactic expr :=
do env  ← get_env,
   decl ← env.get c,
   let num := decl.univ_params.length,
   ls   ← mk_num_meta_univs num,
   return (expr.const c ls)

/-- Apply the constant `c` -/
meta def applyc (c : name) (cfg : apply_cfg := {}) : tactic unit :=
do c ← mk_const c, apply c cfg, skip

meta def eapplyc (c : name) : tactic unit :=
do c ← mk_const c, eapply c, skip

meta def save_const_type_info (n : name) {elab : bool} (ref : expr elab) : tactic unit :=
try (do c ← mk_const n, save_type_info c ref)

/-- Create a fresh universe `?u`, a metavariable `?T : Type.{?u}`,
   and return metavariable `?M : ?T`.
   This action can be used to create a meta-variable when
   we don't know its type at creation time -/
meta def mk_mvar : tactic expr :=
do u ← mk_meta_univ,
   t ← mk_meta_var (expr.sort u),
   mk_meta_var t

/-- Makes a sorry macro with a meta-variable as its type. -/
meta def mk_sorry : tactic expr := do
u ← mk_meta_univ,
t ← mk_meta_var (expr.sort u),
return $ expr.mk_sorry t

/-- Closes the main goal using sorry. -/
meta def admit : tactic unit :=
target >>= exact ∘ expr.mk_sorry

meta def mk_local' (pp_name : name) (bi : binder_info) (type : expr) : tactic expr := do
uniq_name ← mk_fresh_name,
return $ expr.local_const uniq_name pp_name bi type

meta def mk_local_def (pp_name : name) (type : expr) : tactic expr :=
mk_local' pp_name binder_info.default type

meta def mk_local_pis : expr → tactic (list expr × expr)
| (expr.pi n bi d b) := do
  p ← mk_local' n bi d,
  (ps, r) ← mk_local_pis (expr.instantiate_var b p),
  return ((p :: ps), r)
| e := return ([], e)

private meta def get_pi_arity_aux : expr → tactic nat
| (expr.pi n bi d b) :=
  do m     ← mk_fresh_name,
     let l := expr.local_const m n bi d,
     new_b ← whnf (expr.instantiate_var b l),
     r     ← get_pi_arity_aux new_b,
     return (r + 1)
| e                  := return 0

/-- Compute the arity of the given (Pi-)type -/
meta def get_pi_arity (type : expr) : tactic nat :=
whnf type >>= get_pi_arity_aux

/-- Compute the arity of the given function -/
meta def get_arity (fn : expr) : tactic nat :=
infer_type fn >>= get_pi_arity

meta def triv : tactic unit := mk_const `trivial >>= exact

notation `dec_trivial` := of_as_true (by tactic.triv)

meta def by_contradiction (H : name) : tactic expr :=
do tgt ← target,
  tgt_wh ← whnf tgt reducible, -- to ensure that `not` in `ne` is found
  (match_not tgt_wh $> ()) <|>
  (mk_mapp `decidable.by_contradiction [some tgt, none] >>= eapply >> skip) <|>
  (mk_mapp `classical.by_contradiction [some tgt] >>= eapply >> skip) <|>
  fail "tactic by_contradiction failed, target is not a proposition",
  intro H

private meta def generalizes_aux (md : transparency) : list expr → tactic unit
| []      := skip
| (e::es) := generalize e `x md >> generalizes_aux es

meta def generalizes (es : list expr) (md := semireducible) : tactic unit :=
generalizes_aux md es

private meta def kdependencies_core (e : expr) (md : transparency) : list expr → list expr → tactic (list expr)
| []      r := return r
| (h::hs) r :=
  do type ← infer_type h,
     d ← kdepends_on type e md,
     if d then kdependencies_core hs (h::r)
     else kdependencies_core hs r

/-- Return all hypotheses that depends on `e`
    The dependency test is performed using `kdepends_on` with the given transparency setting. -/
meta def kdependencies (e : expr) (md := reducible) : tactic (list expr) :=
do ctx ← local_context, kdependencies_core e md ctx []

/-- Revert all hypotheses that depend on `e` -/
meta def revert_kdependencies (e : expr) (md := reducible) : tactic nat :=
kdependencies e md >>= revert_lst

meta def revert_kdeps (e : expr) (md := reducible) :=
revert_kdependencies e md

/-- Postprocess the output of `cases_core`:

- The third component of each tuple in the input list (the list of
  substitutions) is dropped since we don't use it anywhere.
- The second component (the list of new hypotheses) is filtered: any expression
  that is not a local constant is dropped. We only use the new hypotheses for
  the renaming functionality of `case`, so we want to keep only those
  "new hypotheses" that are, in fact, local constants. -/
private meta def cases_postprocess (hs : list (name × list expr × list (name × expr)))
  : list (name × list expr) :=
hs.map $ λ ⟨n, hs, _⟩, (n, hs.filter (λ h, h.is_local_constant))

/-- Similar to `cases_core`, but `e` doesn't need to be a hypothesis.
    Remark, it reverts dependencies using `revert_kdeps`.

    Two different transparency modes are used `md` and `dmd`.
    The mode `md` is used with `cases_core` and `dmd` with `generalize` and `revert_kdeps`.

    It returns the constructor names associated with each new goal and the newly
    introduced hypotheses. Note that while `cases_core` may return "new
    hypotheses" that are not local constants, this tactic only returns local
    constants.
-/
meta def cases (e : expr) (ids : list name := []) (md := semireducible) (dmd := semireducible) : tactic (list (name × list expr)) :=
if e.is_local_constant then
  do r ← cases_core e ids md, return $ cases_postprocess r
else do
  n ← revert_kdependencies e dmd,
  x ← get_unused_name,
  (tactic.generalize e x dmd)
  <|>
  (do t ← infer_type e,
      tactic.assertv x t e,
      get_local x >>= tactic.revert,
      return ()),
  h ← tactic.intro1,
  focus1 $ do
    r ← cases_core h ids md,
    hs' ← all_goals (intron' n),
    return $ cases_postprocess $ r.map₂ (λ ⟨n, hs, x⟩ hs', (n, hs ++ hs', x)) hs'

/-- The same as `exact` except you can add proof holes. -/
meta def refine (e : pexpr) : tactic unit :=
do tgt : expr ← target,
   to_expr ``(%%e : %%tgt) tt >>= exact

/--
`by_cases p h` splits the main goal into two cases, assuming `h : p` in the
first branch, and `h : ¬ p` in the second branch. The expression `p` needs to
be a proposition.

The produced proof term is `dite p ?m_1 ?m_2`.
-/
meta def by_cases (e : expr) (h : name) : tactic unit := do
dec_e ← mk_app ``decidable [e] <|> fail "by_cases tactic failed, type is not a proposition",
inst ← mk_instance dec_e <|> pure `(classical.prop_decidable %%e),
tgt ← target,
expr.sort tgt_u ← infer_type tgt >>= whnf,
g1 ← mk_meta_var (e.imp tgt),
g2 ← mk_meta_var (`(¬ %%e).imp tgt),
focus1 $ do
  exact $ expr.const ``dite [tgt_u] tgt e inst g1 g2,
  set_goals [g1, g2],
  all_goals' $ intro h >> skip

meta def funext_core : list name → bool → tactic unit
| []  tt       := return ()
| ids only_ids := try $
   do some (lhs, rhs) ← expr.is_eq <$> (target >>= whnf),
      applyc `funext,
      id ← if ids.empty ∨ ids.head = `_ then do
             (expr.lam n _ _ _) ← whnf lhs
               | pure `_,
             return n
           else return ids.head,
      intro id,
      funext_core ids.tail only_ids

meta def funext : tactic unit :=
funext_core [] ff

meta def funext_lst (ids : list name) : tactic unit :=
funext_core ids tt

private meta def get_undeclared_const (env : environment) (base : name) : ℕ → name | i :=
let n := base <.> ("_aux_" ++ repr i) in
if ¬env.contains n then n
else get_undeclared_const (i+1)

meta def new_aux_decl_name : tactic name := do
env ← get_env, n ← decl_name,
return $ get_undeclared_const env n 1

private meta def mk_aux_decl_name : option name → tactic name
| none          := new_aux_decl_name
| (some suffix) := do p ← decl_name, return $ p ++ suffix

meta def abstract (tac : tactic unit) (suffix : option name := none) (zeta_reduce := tt) : tactic unit :=
do fail_if_no_goals,
   gs ← get_goals,
   type ← if zeta_reduce then target >>= zeta else target,
   is_lemma ← is_prop type,
   m ← mk_meta_var type,
   set_goals [m],
   tac,
   n ← num_goals,
   when (n ≠ 0) (fail "abstract tactic failed, there are unsolved goals"),
   set_goals gs,
   val ← instantiate_mvars m,
   val ← if zeta_reduce then zeta val else return val,
   c   ← mk_aux_decl_name suffix,
   e   ← add_aux_decl c type val is_lemma,
   exact e

/-- `solve_aux type tac` synthesize an element of 'type' using tactic 'tac' -/
meta def solve_aux {α : Type} (type : expr) (tac : tactic α) : tactic (α × expr) :=
do m ← mk_meta_var type,
   gs ← get_goals,
   set_goals [m],
   a ← tac,
   set_goals gs,
   return (a, m)

/-- Return tt iff 'd' is a declaration in one of the current open namespaces -/
meta def in_open_namespaces (d : name) : tactic bool :=
do ns  ← open_namespaces,
   env ← get_env,
   return $ ns.any (λ n, n.is_prefix_of d) && env.contains d

/-- Execute tac for 'max' "heartbeats". The heartbeat is approx. the maximum number of
    memory allocations (in thousands) performed by 'tac'. This is a deterministic way of interrupting
    long running tactics. -/
meta def try_for {α} (max : nat) (tac : tactic α) : tactic α :=
λ s,
match _root_.try_for max (tac s) with
| some r := r
| none   := mk_exception "try_for tactic failed, timeout" none s
end

/-- Execute `tac` for `max` milliseconds. Useful due to variance
    in the number of heartbeats taken by various tactics. -/
meta def try_for_time {α} (max : nat) (tac : tactic α) : tactic α :=
λ s,
match _root_.try_for_time max (tac s) with
| some r := r
| none   := mk_exception "try_for_time tactic failed, timeout" none s
end


meta def updateex_env (f : environment → exceptional environment) : tactic unit :=
do env ← get_env,
   env ← returnex $ f env,
   set_env env

/-- Add a new inductive datatype to the environment
   name, universe parameters, number of parameters, type, constructors (name and type), is_meta -/
meta def add_inductive (n : name) (ls : list name) (p : nat) (ty : expr) (is : list (name × expr))
  (is_meta : bool := ff) : tactic unit :=
updateex_env $ λe, e.add_inductive n ls p ty is is_meta

meta def add_meta_definition (n : name) (lvls : list name) (type value : expr) : tactic unit :=
add_decl (declaration.defn n lvls type value reducibility_hints.abbrev ff)

/-- add declaration `d` as a protected declaration -/
meta def add_protected_decl (d : declaration) : tactic unit :=
updateex_env $ λ e, e.add_protected d

/-- check if `n` is the name of a protected declaration -/
meta def is_protected_decl (n : name) : tactic bool :=
do env ← get_env,
   return $ env.is_protected n

/-- `add_defn_equations` adds a definition specified by a list of equations.

  The arguments:
    * `lp`: list of universe parameters
    * `params`: list of parameters (binders before the colon);
    * `fn`: a local constant giving the name and type of the declaration
      (with `params` in the local context);
    * `eqns`: a list of equations, each of which is a list of patterns
      (constructors applied to new local constants) and the branch
      expression;
    * `is_meta`: is the definition meta?


  `add_defn_equations` can be used as:

      do my_add ← mk_local_def `my_add `(ℕ → ℕ),
          a ← mk_local_def `a ℕ,
          b ← mk_local_def `b ℕ,
          add_defn_equations [a] my_add
              [ ([``(nat.zero)], a),
                ([``(nat.succ %%b)], my_add b) ])
              ff -- non-meta

  to create the following definition:

      def my_add (a : ℕ) : ℕ → ℕ
      | nat.zero := a
      | (nat.succ b) := my_add b
-/
meta def add_defn_equations (lp : list name) (params : list expr) (fn : expr)
                            (eqns : list (list pexpr × expr)) (is_meta : bool) : tactic unit :=
do opt ← get_options,
   updateex_env $ λ e, e.add_defn_eqns opt lp params fn eqns is_meta

/-- Get the revertible part of the local context. These are the hypotheses that
appear after the last frozen local instance in the local context. We call them
revertible because `revert` can revert them, unlike those hypotheses which occur
before a frozen instance. -/
meta def revertible_local_context : tactic (list expr) :=
do ctx ← local_context,
   frozen ← frozen_local_instances,
   pure $
     match frozen with
     | none := ctx
     | some [] := ctx
     | some (h :: _) := ctx.after (eq h)
     end

/--
Rename local hypotheses according to the given `name_map`. The `name_map`
contains as keys those hypotheses that should be renamed; the associated values
are the new names.

This tactic can only rename hypotheses which occur after the last frozen local
instance. If you need to rename earlier hypotheses, try
`unfreezing (rename_many ...)`.

If `strict` is true, we fail if `name_map` refers to hypotheses that do not
appear in the local context or that appear before a frozen local instance.
Conversely, if `strict` is false, some entries of `name_map` may be silently
ignored.

If `use_unique_names` is true, the keys of `name_map` should be the unique names
of hypotheses to be renamed. Otherwise, the keys should be display names.

Note that we allow shadowing, so renamed hypotheses may have the same name
as other hypotheses in the context. If `use_unique_names` is false and there are
multiple hypotheses with the same display name in the context, they are all
renamed.
-/
meta def rename_many (renames : name_map name) (strict := tt) (use_unique_names := ff)
: tactic unit :=
do let hyp_name : expr → name :=
     if use_unique_names then expr.local_uniq_name else expr.local_pp_name,
   ctx ← revertible_local_context,
   -- The part of the context after (but including) the first hypthesis that
   -- must be renamed.
   let ctx_suffix := ctx.drop_while (λ h, (renames.find $ hyp_name h).is_none),
   when strict $ do {
     let ctx_names := rb_map.set_of_list (ctx_suffix.map hyp_name),
     let invalid_renames :=
       (renames.to_list.map prod.fst).filter (λ h, ¬ ctx_names.contains h),
     when ¬ invalid_renames.empty $ fail $ format.join
       [ "Cannot rename these hypotheses:\n"
       , format.join $ (invalid_renames.map to_fmt).intersperse ", "
       , format.line
       , "This is because these hypotheses either do not occur in the\n"
       , "context or they occur before a frozen local instance.\n"
       , "In the latter case, try `unfreezingI { ... }`."
       ]
   },
   -- The new names for all hypotheses in ctx_suffix.
   let new_names :=
     ctx_suffix.map $ λ h,
       (renames.find $ hyp_name h).get_or_else h.local_pp_name,
   revert_lst ctx_suffix,
   intro_lst new_names,
   pure ()

/--
Rename a local hypothesis. This is a special case of `rename_many`;
see there for caveats.
-/
meta def rename (curr : name) (new : name) : tactic unit :=
rename_many (rb_map.of_list [⟨curr, new⟩])

/--
Rename a local hypothesis. Unlike `rename` and `rename_many`, this tactic does
not preserve the order of hypotheses. Its implementation is simpler (and
therefore probably faster) than that of `rename`.
-/
meta def rename_unstable (curr : name) (new : name) : tactic unit :=
do h ← get_local curr,
   n ← revert h,
   intro new,
   intron (n - 1)

/--
"Replace" hypothesis `h : type` with `h : new_type` where `eq_pr` is a proof
that (type = new_type). The tactic actually creates a new hypothesis
with the same user facing name, and (tries to) clear `h`.
The `clear` step fails if `h` has forward dependencies. In this case, the old `h`
will remain in the local context. The tactic returns the new hypothesis. -/
meta def replace_hyp (h : expr) (new_type : expr) (eq_pr : expr) (tag : name := `unit.star) : tactic expr :=
do h_type ← infer_type h,
   new_h ← assert h.local_pp_name new_type,
   eq_pr_type ← mk_app `eq [h_type, new_type],
   let eq_pr := mk_tagged_proof eq_pr_type eq_pr tag,
   mk_eq_mp eq_pr h >>= exact,
   try $ clear h,
   return new_h

meta def main_goal : tactic expr :=
do g::gs ← get_goals, return g

/-! Goal tagging support -/
meta def with_enable_tags {α : Type} (t : tactic α) (b := tt) : tactic α :=
do old ← tags_enabled,
   enable_tags b,
   r ← t,
   enable_tags old,
   return r

meta def get_main_tag : tactic tag :=
main_goal >>= get_tag

meta def set_main_tag (t : tag) : tactic unit :=
do g ← main_goal, set_tag g t

meta def subst (h : expr) : tactic unit :=
(do guard h.is_local_constant,
    some (α, lhs, β, rhs) ← expr.is_heq <$> infer_type h,
    is_def_eq α β,
    new_h_type ← mk_app `eq [lhs, rhs],
    new_h_pr   ← mk_app `eq_of_heq [h],
    new_h ← assertv h.local_pp_name new_h_type new_h_pr,
    try (clear h),
    subst_core new_h)
<|> subst_core h
end tactic

notation [parsing_only] `command`:max := tactic unit

open tactic

namespace list

meta def for_each {α} : list α → (α → tactic unit) → tactic unit
| []      fn := skip
| (e::es) fn := do fn e, for_each es fn

meta def any_of {α β} : list α → (α → tactic β) → tactic β
| []      fn := failed
| (e::es) fn := do opt_b ← try_core (fn e),
                   match opt_b with
                   | some b := return b
                   | none   := any_of es fn
                   end
end list

/-! Install monad laws tactic and use it to prove some instances. -/

/-- Try to prove with `iff.refl`.-/
meta def order_laws_tac := whnf_target >> intros >> to_expr ``(iff.refl _) >>= exact

meta def monad_from_pure_bind {m : Type u → Type v}
  (pure : Π {α : Type u}, α → m α)
  (bind : Π {α β : Type u}, m α → (α → m β) → m β) : monad m :=
{pure := @pure, bind := @bind}

meta instance : monad task :=
{map := @task.map, bind := @task.bind, pure := @task.pure}

namespace tactic

meta def replace_target (new_target : expr) (pr : expr) (tag : name := `unit.star) : tactic unit :=
do t ← target,
   assert `htarget new_target, swap,
   ht        ← get_local `htarget,
   pr_type   ← mk_app `eq [t, new_target],
   let locked_pr := mk_tagged_proof pr_type pr tag,
   mk_eq_mpr locked_pr ht >>= exact

meta def eval_pexpr (α) [reflected _ α] (e : pexpr) : tactic α :=
to_expr ``(%%e : %%(reflect α)) ff ff >>= eval_expr α

meta def run_simple {α} : tactic_state → tactic α → option α
| ts t := match t ts with
          | (interaction_monad.result.success a ts') := some a
          | (interaction_monad.result.exception _ _ _) := none
          end

end tactic
