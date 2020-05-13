prelude
import init.meta.widget.basic
import init.meta.tactic
import init.meta.expr_address

namespace widget

/-- An alternative to format that keeps structural information about the expression.
For lack of a better name I called it `magic`, rename suggestions welcome.

On tag_expr, note that the given `expr` is _not_ necessarily the subexpression of the root expression that `tactic_state.pp_magic` was
called with. For example if the subexpression is under a binder then all of the `expr.var 0`s will be replaced with
a local not in the local context with the name and type set to that of the binder.
-/
meta inductive magic
| tag_expr : expr.address → expr → magic → magic
| compose : magic → magic → magic
| group : magic → magic
| nest : nat → magic → magic
| highlight : format.color → magic → magic
| format : format → magic

open format
meta def magic.to_fmt : magic → format
| (magic.compose m1 m2) := format.compose (magic.to_fmt m1) (magic.to_fmt m2)
| (magic.group m1) := format.group (magic.to_fmt m1)
| (magic.nest i m) := format.nest i $ magic.to_fmt m
| (magic.highlight c m) := format.highlight (magic.to_fmt m) c
| (magic.format f) := f
| (magic.tag_expr ea e m) := magic.to_fmt m

meta instance magic.has_to_fmt : has_to_format magic := ⟨magic.to_fmt⟩

end widget

open widget

/-- A special version of pp which also preserves expression boundary information. -/
meta constant tactic_state.pp_magic   : tactic_state → expr → magic

meta def tactic.pp_magic : expr → tactic magic
| e := tactic.read >>= λ ts, pure $ tactic_state.pp_magic ts e


