/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import init.meta.widget.interactive_expr

meta def tactic.save_info_with_widgets (p : pos) : tactic unit :=
do s ← tactic.read,
   tactic.save_info_thunk p (λ _, tactic_state.to_format s),
   tactic.save_widget p widget.tactic_state_widget

attribute [vm_override tactic.save_info_with_widgets] tactic.save_info

