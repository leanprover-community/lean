/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.expr
universe u

/-- Quoted expressions. They can be converted into expressions by using a tactic. -/
@[reducible] meta def pexpr := expr ff
protected meta constant pexpr.of_expr  : expr → pexpr

meta constant pexpr.is_placeholder : pexpr → bool
meta constant pexpr.mk_placeholder : pexpr
meta constant pexpr.mk_field_macro : pexpr → name → pexpr
meta constant pexpr.mk_explicit : pexpr → pexpr

/-- `expr.fold e a f`: Traverses each subexpression of `e`. The `nat` passed to the folder `f` is the binder depth. -/
meta constant pexpr.fold {α : Type} : pexpr → α → (pexpr → nat → α → α) → α
/-- `expr.replace e f`
 Traverse over an expr `e` with a function `f` which can decide to replace subexpressions or not.
 For each subexpression `s` in the expression tree, `f s n` is called where `n` is how many binders are present above the given subexpression `s`.
 If `f s n` returns `none`, the children of `s` will be traversed.
 Otherwise if `some s'` is returned, `s'` will replace `s` and this subexpression will not be traversed further.
 -/
meta constant pexpr.replace : pexpr → (pexpr → nat → option pexpr) → pexpr

/-- Choice macros are used to implement overloading. -/
meta constant pexpr.is_choice_macro : pexpr → bool

/-- Information about unelaborated structure instance expressions. -/
meta structure structure_instance_info :=
(struct       : option name := none)
(field_names  : list name)
(field_values : list pexpr)
(sources      : list pexpr := [])

/-- Create a structure instance expression. -/
meta constant pexpr.mk_structure_instance : structure_instance_info → pexpr
meta constant pexpr.get_structure_instance_info : pexpr → option structure_instance_info

meta class has_to_pexpr (α : Sort u) :=
(to_pexpr : α → pexpr)

meta def to_pexpr {α : Sort u} [has_to_pexpr α] : α → pexpr :=
has_to_pexpr.to_pexpr

meta instance : has_to_pexpr pexpr :=
⟨id⟩

meta instance : has_to_pexpr expr :=
⟨pexpr.of_expr⟩

meta instance (α : Sort u) (a : α) : has_to_pexpr (reflected a) :=
⟨pexpr.of_expr ∘ reflected.to_expr⟩
