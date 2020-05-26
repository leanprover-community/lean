/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
prelude
import init.meta.tactic
import init.meta.expr_address
import init.control

universe u

/-- An alternative to format that keeps structural information stored as a tag. -/
meta inductive tagged_format (α : Type u)
| tag       : α → tagged_format → tagged_format
| compose   : tagged_format → tagged_format → tagged_format
| group     : tagged_format → tagged_format
| nest      : nat → tagged_format → tagged_format
| highlight : format.color → tagged_format → tagged_format
| of_format : format → tagged_format

namespace tagged_format

variables {α β : Type u}

protected meta def map (f : α → β) : tagged_format α → tagged_format β
| (compose x y)   := compose (map x) (map y)
| (group x)       := group $ map x
| (nest i x)      := nest i $ map x
| (highlight c x) := highlight c $ map x
| (of_format x)   := of_format x
| (tag a x)       := tag (f a) (map x)

meta instance is_functor: functor tagged_format :=
{ map := @tagged_format.map }

meta def m_untag {t : Type → Type} [monad t] (f : α → format → t format) : tagged_format α → t format
| (compose x y)   := pure format.compose <*> m_untag x <*> m_untag y
| (group x)       := pure format.group <*> m_untag x
| (nest i x)      := pure (format.nest i) <*> m_untag x
| (highlight c x) := pure format.highlight <*> m_untag x <*> pure c
| (of_format x)   := pure $ x
| (tag a x)       := m_untag x >>= f a

meta def untag (f : α → format → format) : tagged_format α → format :=
@m_untag _ id _ f

meta instance has_to_fmt : has_to_format (tagged_format α) :=
⟨tagged_format.untag (λ a f, f)⟩

end tagged_format

/-- tagged_format with information about subexpressions. -/
meta def eformat := tagged_format (expr.address × expr)

/-- A special version of pp which also preserves expression boundary information.

On a tag ⟨e,a⟩, note that the given expr `e` is _not_ necessarily the subexpression of the root
expression that `tactic_state.pp_tagged` was called with. For example if the subexpression is
under a binder then all of the `expr.var 0`s will be replaced with a local constant not in
the local context with the name and type set to that of the binder.-/
meta constant tactic_state.pp_tagged : tactic_state → expr → eformat

meta def tactic.pp_tagged : expr → tactic eformat
| e := tactic.read >>= λ ts, pure $ tactic_state.pp_tagged ts e
