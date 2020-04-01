prelude
import init.meta.tactic init.meta.attribute init.meta.rb_map init.meta.derive

universes u v

namespace interactive

-- meta def tactic_handler.get_state_dflt : tactic unit :=
-- tactic.exact `(pure () : tactic unit)

-- meta def tactic_handler.set_state_dflt : tactic unit :=
-- tactic.exact `(pure : unit → tactic unit)

-- meta structure tactic_handler (state : Type := unit) :=
-- (name : name)
-- [state_has_reflect : has_reflect state]
-- (on_begin : tactic state)
-- (on_end : (state → tactic unit))
-- (get_state : tactic state . tactic_handler.get_state_dflt)
-- (set_state : (state → tactic unit) . tactic_handler.set_state_dflt)

-- attribute [instance] tactic_handler.state_has_reflect
-- attribute [derive has_reflect] tactic_handler

-- meta instance : has_reflect tactic_handler
-- | a := `(_)
-- `({ tactic_handler . name := _, on_begin := _, on_end := _, state := _, get_state := _, set_state := _ })

-- meta instance state.has_reflect (hdl : tactic_handler) [reflected hdl] : has_reflect (option hdl.state) :=
-- @option.has_reflect _ (tactic_handler.has_reflect _)  $ reflected.subst `(tactic_handler.state) `(hdl)

-- #check option.has_reflect
-- #check tactic_handler.has_reflect
open native
open tactic
-- #exit
namespace tactic_handler

-- meta def to_user_attribute
--   {s : Type} (hdl : tactic_handler s)
--   [has_reflect s] [reflected s] :
--   user_attribute unit expr :=
-- { name := hdl.name <.> "store",
--        -- reflect_param := state.has_reflect hdl,
--  -- (tactic_handler.has_reflect hdl hdl),
--   descr := to_string hdl.name ++ " store",
--   parser := fail "do not use" }

-- meta def read_dyn (hdl : _root_.name) : tactic expr :=
-- do c ← mk_const $ hdl <.> "store",
--    e ← eval_expr (user_attribute unit expr) c,
--    e.get_param hdl

-- meta def write_dyn (hdl : _root_.name) (v : expr) : tactic unit :=
-- do c ← mk_const $ hdl <.> "store",
--    infer_type c >>= trace,
--    trace hdl,
--    e ← eval_expr (user_attribute unit expr) c,
--    trace "b",
--    e.set hdl v tt,
--    trace "c"

end tactic_handler


-- @[user_attribute]
-- meta def tactic_handler_attr : user_attribute := -- (rb_map name expr) :=
-- { name := `tactic_handler,
--   descr := "descr",
--   after_set := some $ λ n p _, do
--   { `(tactic_handler %%state) ← tactic.mk_const n >>= infer_type
--       | fail "expecting definition of type `user_attribute`",
--     e ← resolve_name n,
--     df ← to_expr ``(tactic_handler.to_user_attribute %%e),
--     t  ← infer_type df,
--     add_meta_definition (n <.> "store") [] t df,
--     infer_type df >>= trace,
--     set_basic_attribute ``user_attribute (n <.> "store") tt,
--     -- e ← mk_const n,
--     trace "\nAAA",
--     e_store ← mk_const (n <.> "store"),
--     infer_type e_store >>= trace,
--     trace "\nAAA",
--     val ← mk_mapp ``option.none [state],
--     trace "\nAAA",
--     let none_e : expr := reflect $ @none ℕ,
--     let v_e : expr := reflect val,
--     let n_e : expr := reflect n,
--     let b_e : expr := reflect tt,
--     x ← mk_mapp ``user_attribute.set [none,none,none,e_store,n_e,v_e,b_e,none_e],
--     tac ← eval_expr (tactic unit) x,
--     tac,
--     trace "\nAAA",
--     -- x ← mk_app ``user_attribute.set [e_store,n_e,v_e,b_e],
--     infer_type x >>= trace,
--     attr ← eval_expr (user_attribute unit expr) e_store,
--     -- infer_type attr >>= trace,
--     trace "state",
--     -- n_hdl ← mk_app ``tactic_handler.name [e] >>= eval_expr name,
--     -- tactic_handler.write_dyn n val,
--     trace "state" },
-- }
-- #check @user_attribute.set
-- #exit
-- set_option trace.app_builder true
-- @[tactic_handler]
-- meta def my_tactic_handler : tactic_handler :=
-- { name := `my_tactic_handler,
--   on_begin := tactic.trace "begin",
--   on_end := λ _, tactic.trace "end", }

meta def foo : tactic unit := do
let n := `foo,
let n := reflect n,
trace_state,
add_decl $ mk_definition `foo [] `(name) n,
mk_const `foo >>= exact

meta class is_advice_type (α : Type) :=
-- [type_reflect : has_reflect α]
(to_format : α → format)
(to_format_name : name . foo)
-- (combine : α → α → α)

meta instance : is_advice_type nat :=
{ to_format := to_fmt, }
#check foo
@[derive has_reflect]
meta structure advice :=
(to_format : name)
(val : expr)

attribute [instance] is_advice_type.type_reflect

@[user_attribute]
private meta def lint_advice_attr : user_attribute unit (list (pos × advice)) := -- (rb_map name expr) :=
{ name := `_lint_advice,
  descr := "descr",
  parser := fail "do not use" }

def lint_advice_carrier := ()

run_cmd lint_advice_attr.set ``lint_advice_carrier [] tt

-- end interactive


-- namespace interactive

open tactic

declare_trace lint.all
declare_trace lint.tactic

meta def executor.combine_advice_dflt : tactic unit :=
tactic.refine ``(λ _ _, ())

meta def executor.default_resolve (pre n : name) : tactic name :=
if is_trace_enabled_for `lint.all = tt ∨ is_trace_enabled_for (`lint ++ pre) = tt
  then resolve_constant (pre <.> "linter" ++ n) <|>
       pure (pre <.> "interactive" ++ n)
  else pure $ pre <.> "interactive" ++ n

-- meta def executor.resolve_tactic_name_dfl : tactic unit :=
-- applyc ``executor.default_resolve
-- do `(name → (%%m : Type → Type*) name) ← tactic.target,
--    let n := m.get_app_fn.const_name,
--    let n : reflected n := reflect n,
--    e ← mk_mapp ``interactive.executor.default_resolve [m,none,n],
--    exact e

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
(advice_type : Type := unit)
[inhabited : inhabited config_type]
-- [advice : monoid]
(combine_advice : advice_type → advice_type → advice_type . executor.combine_advice_dflt)
(format_advice : advice_type → format)
(execute_with : config_type → m punit → tactic.{u} punit)
(resolve_tactic_name : name → name → tactic name := executor.default_resolve)

attribute [inline] executor.execute_with

@[inline]
meta def executor.execute_explicit (m : Type → Type v)
   [monad m] [e : executor m] : m punit → tactic punit :=
executor.execute_with e.inhabited.default

@[inline]
meta def executor.execute_with_explicit (m : Type → Type v)
   [monad m] [executor m] : executor.config_type m → m punit → tactic punit :=
executor.execute_with

/-- Default `executor` instance for `tactic`s themselves -/
meta instance : executor tactic :=
{ config_type := punit,
  inhabited := ⟨()⟩,
  execute_with := λ _ tac, tac,
  -- resolve_tactic_name := λ n, do
  --   trace  ("resolve " ++ to_string n) $
  --   pure $ `tactic.interactive ++ n
 }

end interactive

namespace tactic

notation `‹` p `›` := (by assumption : p)
notation `dec_trivial` := of_as_true (by tactic.triv)

end tactic
