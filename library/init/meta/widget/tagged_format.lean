/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import init.meta.widget.basic
import init.meta.tactic
import init.meta.expr_address

namespace widget

/-- An alternative to format that keeps structural information stored as a tag. -/
meta inductive tagged_format (α : Type)
| tag : α → tagged_format → tagged_format
| compose : tagged_format → tagged_format → tagged_format
| group : tagged_format → tagged_format
| nest : nat → tagged_format → tagged_format
| highlight : format.color → tagged_format → tagged_format
| format : format → tagged_format

variables {α : Type}

open format
protected meta def tagged_format.to_fmt: tagged_format α → format
| (tagged_format.compose m1 m2) := format.compose (tagged_format.to_fmt m1) (tagged_format.to_fmt m2)
| (tagged_format.group m1)      := format.group $ tagged_format.to_fmt m1
| (tagged_format.nest i m)      := format.nest i $ tagged_format.to_fmt m
| (tagged_format.highlight c m) := format.highlight (tagged_format.to_fmt m) c
| (tagged_format.format f)      := f
| (tagged_format.tag a m)       := tagged_format.to_fmt m

meta instance tagged_format.has_to_fmt : has_to_format (tagged_format α) := ⟨tagged_format.to_fmt⟩

end widget

open widget

/-- tagged_format with information about subexpressions. -/
meta def eformat := tagged_format (expr.address × expr)

/-- A special version of pp which also preserves expression boundary information.

On a tag ⟨e,a⟩, note that the given expr `e` is _not_ necessarily the subexpression of the root
expression that `tactic_state.pp_tagged` was called with. For example if the subexpression is
under a binder then all of the `expr.var 0`s will be replaced with a local not in the local context
with the name and type set to that of the binder.-/
meta constant tactic_state.pp_tagged : tactic_state → expr → eformat

meta def tactic.pp_tagged : expr → tactic eformat
| e := tactic.read >>= λ ts, pure $ tactic_state.pp_tagged ts e
