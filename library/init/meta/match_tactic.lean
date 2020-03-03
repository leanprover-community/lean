/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.interactive_base init.function

namespace tactic
/-- A pattern is an expression `target` containing temporary metavariables.
A pattern also contains a list of `outputs` which also depend on these temporary metavariables.
When we run `match p e`, the system will match `p.target` with `e` and assign
the temporary metavariables. It then returns the outputs with the assigned variables.

## Fields

- `target` Term to match. Contains temporary metavariables.
- `uoutput` List of universes that are returned on a successful match.
- `moutput` List of expressions that are returned on a successful match.
- `nuvars` Number of (temporary) universe metavariables in this pattern.
- `nmvars` Number of (temporary) metavariables in this pattern.

## Example

The pattern for `list.cons h t` returning `h` and `t` would be
```
{ target  := `(@list.cons ?x_0 ?x_1 ?x_2),
  uoutput := [],
  moutput := [?x_1,?x_2],
  nuvars  := 0,
  nmvars  := 3
}
```

-/
meta structure pattern :=
(target : expr)
(uoutput : list level)
(moutput : list expr)
(nuvars : nat)
(nmvars : nat)

/-- `mk_pattern umetas emetas target uoutput eoutput` creates a new pattern. The arguments are
- `umetas` a list of level params to be replaced with temporary universe metavariables.
- `emetas` a list of local constants to be replaced with temporary metavariables.
- `target` the expression to be matched.
- `uoutput` a list of levels to return upon matching. Fails if this depends on metavariables.
- `eoutput` a list of expressions to return upon matching. Fails if this depends on metavariables.

The procedure is as follows:
1. Convert all metavariables in `target` to temporary metavariables.
2. For each item in `umetas` amd `emetas`, create a temporary
   metavariable and replace each instance of the item in `target` with a temporary metavariable
3. Replace these instances in `uoutput` and `eoutput` too.
4. Return these replaced versions as a `pattern`.

## Example
Let `h`,`t` be exprs with types `α` and `list α` respectively.
Then `mk_pattern [] [α,h,t] `(@list.cons α h t) [] [h,t]` would `match_pattern` against any expr which is a list.cons constructor and return the head and tail arguments.
-/
meta constant mk_pattern (umetas : list level) (emetas : list expr) (target : expr) (uoutput :list level) (eoutput : list expr) : tactic pattern
/-- `mk_pattern p e m` matches (pattern.target p) and e using transparency m.
   If the matching is successful, then return the instantiation of `pattern.output p`.
   The tactic fails if not all (temporary) meta-variables are assigned. -/
meta constant match_pattern (p : pattern) (e : expr) (m : transparency := reducible) : tactic (list level × list expr)

open expr

private meta def to_pattern_core : expr → tactic (expr × list expr)
| (lam n bi d b) := do
   id         ← mk_fresh_name,
   let x     := local_const id n bi d,
   let new_b := instantiate_var b x,
   (p, xs) ← to_pattern_core new_b,
   return (p, x::xs)
| e              := return (e, [])

/-- Given a pre-term of the form `λ x₁ ... xₙ, t[x₁, ..., xₙ]`, converts it
   into the pattern `t[?x₁, ..., ?xₙ]` with outputs `[?x₁, ..., ?xₙ]` -/
meta def pexpr_to_pattern (p : pexpr) : tactic pattern :=
do /- Remark: in the following to_expr, we allow metavars but we do *not* create new goals for them.
      mk_pattern will convert them into temporary metavars. -/
   e ← to_expr p tt ff,
   (new_p, xs) ← to_pattern_core e,
   mk_pattern [] xs new_p [] xs

/-- Convert pre-term into a pattern and try to match e.
   Given p of the form `λ x₁ ... xₙ, t[x₁, ..., xₙ]`, a successful
   match will produce a list of length n. -/
meta def match_expr (p : pexpr) (e : expr) (m := reducible) : tactic (list expr) :=
do new_p ← pexpr_to_pattern p,
   prod.snd <$> match_pattern new_p e m

private meta def match_subexpr_core (m : transparency) : pattern → list expr → tactic (list expr)
| p []      := failed
| p (e::es) :=
  (prod.snd <$> match_pattern p e m)
  <|>
  match_subexpr_core p es
  <|>
  if is_app e then match_subexpr_core p (get_app_args e)
  else failed

/-- Similar to match_expr, but it tries to match a subexpression of e.
   Remark: the procedure does not go inside binders. -/
meta def match_subexpr (p : pexpr) (e : expr) (m := reducible) : tactic (list expr) :=
do new_p ← pexpr_to_pattern p,
   match_subexpr_core m new_p [e]

/-- Match the main goal target. -/
meta def match_target (p : pexpr) (m := reducible) : tactic (list expr) :=
do t ← target, match_expr p t m

/-- Match a subterm in the main goal target. -/
meta def match_target_subexpr (p : pexpr) (m := reducible) : tactic (list expr) :=
do t ← target, match_subexpr p t m

private meta def match_hypothesis_core (m : transparency) : pattern → list expr → tactic (expr × list expr)
| p []      := failed
| p (h::hs) := do
  h_type ← infer_type h,
  (do r ← match_pattern p h_type m, return (h, r.snd))
  <|>
  match_hypothesis_core p hs

/-- Match hypothesis in the main goal target.
   The result is pair (hypothesis, substitution). -/
meta def match_hypothesis (p : pexpr) (m := reducible) : tactic (expr × list expr) :=
do ctx ← local_context,
   new_p ← pexpr_to_pattern p,
   match_hypothesis_core m new_p ctx

meta instance : has_to_tactic_format pattern :=
⟨λp, do
  t ← pp p.target,
  mo ← pp p.moutput,
  uo ← pp p.uoutput,
  u ← pp p.nuvars,
  m ← pp p.nmvars,
  return format!"pattern.mk ({t}) {uo} {mo} {u} {m}" ⟩

end tactic
