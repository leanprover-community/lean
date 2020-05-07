prelude
import init.meta.tactic
import init.meta.widget.interactive_expr

universe u

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
meta instance : executor tactic :=
{ config_type := unit,
  inhabited := ⟨()⟩,
  execute_with := λ _, id }

end interactive

meta constant tactic.save_widget : pos → component tactic_state string → tactic unit

namespace tactic

meta def save_info (p : pos) : tactic unit :=
do s ← read,
   tactic.save_info_thunk p (λ _, tactic_state.to_format s),
   tactic.save_widget p widget.tactic_state_widget

notation `‹` p `›` := (by assumption : p)

notation `dec_trivial` := of_as_true (by tactic.triv)

end tactic