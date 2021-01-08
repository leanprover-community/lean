/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.meta.tactic init.meta.has_reflect init.control.alternative

namespace lean

-- TODO: make inspectable (and pure)
meta constant parser_state : Type
meta constant parser_state.env     : parser_state → environment
meta constant parser_state.options : parser_state → options
meta constant parser_state.cur_pos : parser_state → pos

@[reducible] meta def parser := interaction_monad parser_state
@[reducible] meta def parser_result := interaction_monad.result parser_state

open interaction_monad
open interaction_monad.result

namespace parser

variable {α : Type}

protected meta def get_state : parser parser_state := λ σ, success σ σ

meta def val (p : lean.parser (reflected_value α)) : lean.parser α :=
reflected_value.val <$> p

protected meta class reflectable (p : parser α) :=
(full : parser (reflected_value α))

namespace reflectable

meta def expr {p : parser α} (r : reflectable p) : parser expr :=
reflected_value.expr <$> r.full

meta def to_parser {p : parser α} (r : reflectable p) : parser α :=
val r.full

end reflectable

meta def get_env : parser environment :=
λ s, success s.env s

meta constant set_env : environment → parser unit

/-- Make sure the next token is an identifier, consume it, and
    produce the quoted name `t, where t is the identifier. -/
meta constant ident : parser name
/-- Make sure the next token is a small nat, consume it, and produce it -/
meta constant small_nat : parser nat
/-- Check that the next token is `tk` and consume it. `tk` must be a registered token. -/
meta constant tk (tk : string) : parser unit
/-- Parse an unelaborated expression using the given right-binding power.
When `pat := tt`, the expression is parsed as a pattern, i.e. local
constants are not checked. -/
protected meta constant pexpr (rbp := std.prec.max) (pat := ff) : parser pexpr


/-- a variable to local scope -/
meta constant add_local (v: expr) : parser unit
meta constant add_local_level (v: name) : parser unit
meta constant list_include_var_names : parser (list name)
meta constant list_available_include_vars : parser (list expr)
meta constant include_var : name → parser unit
meta constant omit_var : name → parser unit

meta constant push_local_scope : parser unit
meta constant pop_local_scope : parser unit

/--
Run the parser in a local declaration scope.

Local declarations added via `add_local` do not propagate outside of this scope.
-/
@[inline]
meta def with_local_scope {α} (p : parser α) : parser α :=
interaction_monad.bracket push_local_scope p pop_local_scope

protected meta constant itactic_reflected : parser (reflected_value (tactic unit))

/-- Parse an interactive tactic block: `begin` .. `end` -/
@[reducible] protected meta def itactic : parser (tactic unit) := val parser.itactic_reflected

/-- Do not report info from content parsed by `p`. -/
meta constant skip_info (p : parser α) : parser α
/-- Set goal info position of content parsed by `p` to current position. Nested calls take precedence. -/
meta constant set_goal_info_pos (p : parser α) : parser α

/-- Return the current parser position without consuming any input. -/
meta def cur_pos : parser pos := λ s, success (parser_state.cur_pos s) s

/-- Temporarily replace input of the parser state, run `p`, and return remaining input. -/
meta constant with_input (p : parser α) (input : string) : parser (α × string)

/-- Parse a top-level command. -/
meta constant command_like : parser unit

meta def parser_orelse (p₁ p₂ : parser α) : parser α :=
λ s,
let pos₁ := parser_state.cur_pos s in
result.cases_on (p₁ s)
  success
  (λ e₁ ref₁ s',
    let pos₂ := parser_state.cur_pos s' in
    if pos₁ ≠ pos₂ then
      exception e₁ ref₁ s'
    else result.cases_on (p₂ s)
     success
     exception)

meta instance : alternative parser :=
{ failure := @interaction_monad.failed _,
  orelse  := @parser_orelse,
  ..interaction_monad.monad }


-- TODO: move
meta def {u v} many {f : Type u → Type v} [monad f] [alternative f] {a : Type u} : f a → f (list a)
| x := (do y ← x,
           ys ← many x,
           return $ y::ys) <|> pure list.nil

local postfix `?`:100 := optional
local postfix `*`:100 := many

meta def sep_by : parser unit → parser α → parser (list α)
| s p := (list.cons <$> p <*> (s *> p)*) <|> return []

meta constant of_tactic : tactic α → parser α

meta instance : has_coe (tactic α) (parser α) :=
⟨of_tactic⟩

namespace reflectable

meta instance cast (p : lean.parser (reflected_value α)) : reflectable (val p) :=
{full := p}

meta instance has_reflect [r : has_reflect α] (p : lean.parser α) : reflectable p :=
{full := do rp ← p, return ⟨rp⟩}

meta instance optional {α : Type} [reflected α] (p : parser α)
  [r : reflectable p] : reflectable (optional p) :=
{full := reflected_value.subst some <$> r.full <|> return ⟨none⟩}

end reflectable

meta def reflect (p : parser α) [r : reflectable p] : parser expr :=
r.expr

meta constant run {α} : parser α → tactic α

meta def run_with_input {α} : parser α → string → tactic α := λ p s,
prod.fst <$> (run (with_input p s) )

meta def mk_parser_state : tactic lean.parser_state :=
lean.parser.run_with_input lean.parser.get_state ""

end parser
end lean
