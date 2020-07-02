/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import init.meta.widget.basic
import init.meta.lean.parser
import init.meta.interactive_base
import init.data.punit
open lean
open lean.parser
open interactive
open tactic
open widget

/-- Accepts terms with the type `component tactic_state empty` or `html empty` and
renders them interactively. -/
@[user_command]
meta def show_widget_cmd (x : parse $ tk "#html") : parser unit := do
  ⟨l,c⟩ ← cur_pos,
  y ← parser.pexpr,
  comp ← parser.of_tactic ((do
    tactic.eval_pexpr (component tactic_state empty) y
  ) <|> (do
    htm : html empty ← tactic.eval_pexpr (html empty) y,
    c : component unit empty ← pure $ component.stateless (λ _, [htm]),
    pure $ component.ignore_props $ component.ignore_action $ c
  )),
  save_widget ⟨l,c - ("#html").length - 1⟩ comp,
  trace "successfully rendered widget"
  pure ()

run_cmd skip
