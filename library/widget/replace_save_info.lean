/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
import .interactive_expr
open tactic

meta def tactic.save_info2 (p : pos) : tactic unit :=
do s ← read,
   tactic.trace "saving info",
   tactic.save_info_thunk p (λ _, tactic_state.to_format s),
   tactic.save_widget p widget.tactic_state_widget

attribute [vm_override tactic.save_info2] tactic.save_info

run_cmd skip
