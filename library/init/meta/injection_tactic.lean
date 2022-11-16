/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jannis Limperg
-/
prelude
import init.meta.tactic

namespace tactic

open expr

/-- Given a local constant `H : C x₁ ... xₙ = D y₁ ... yₘ`, where `C` and `D` are
fully applied constructors, `injection_with H ns base offset` does the
following:

- If `C ≠ D`, it solves the goal (using the no-confusion rule).
- If `C = D` (and thus `n = m`), it adds hypotheses
  `h₁ : x₁ = y₁, ..., hₙ : xₙ = yₙ` to the local context. Names for the `hᵢ`
  are taken from `ns`. If `ns` does not contain enough names, then the names
  are derived from `base` and `offset` (by default `h_1`, `h_2` etc.; see
  `intro_fresh`).
- Special case: if `C = D` and `n = 0` (i.e. the constructors have no
  arguments), the hypothesis `h : true` is added to the context.

`injection_with` returns the new hypotheses and the leftover names from `ns`
(i.e. those names that were not used to name the new hypotheses). If (and only
if) the goal was solved, the list of new hypotheses is empty.
-/
meta def injection_with (h : expr) (ns : list name)
  (base := `h) (offset := some 1) : tactic (list expr × list name) :=
do
  H ← infer_type h,
  (lhs, rhs, constructor_left, constructor_right, inj_name) ← do {
    (lhs, rhs) ← match_eq H,
    lhs ← whnf_ginductive lhs,
    rhs ← whnf_ginductive rhs,
    env ← get_env,
    (const constructor_left _) ← pure $ get_app_fn lhs,
    (const constructor_right _) ← pure $ get_app_fn rhs,
    inj_name ← resolve_constant $ constructor_left ++ "inj_arrow",
    pure (lhs, rhs, constructor_left, constructor_right, inj_name)
  } <|> fail
    "injection tactic failed, argument must be an equality proof where lhs and rhs are of the form (c ...), where c is a constructor",
  if constructor_left = constructor_right then do
    -- C.inj_arrow, for a given constructor C of datatype D, has type
    --
    --     ∀ (A₁ ... Aₙ) (x₁ ... xₘ) (y₁ ... yₘ), C x₁ ... xₘ = C y₁ ... yₘ
    --       → ∀ ⦃P : Sort u⦄, (x₁ = y₁ → ... → yₖ = yₖ → P) → P
    --
    -- where the Aᵢ are parameters of D and the xᵢ/yᵢ are arguments of C.
    -- Note that if xᵢ/yᵢ are propositions, no equation is generated, so the
    -- number of equations is not necessarily the constructor arity.

    -- First, we find out how many equations we need to intro later.
    inj ← mk_const inj_name,
    inj_type ← infer_type inj,
    inj_arity ← get_pi_arity inj_type,
    let num_equations :=
      (inj_type.nth_binding_body (inj_arity - 1)).binding_domain.pi_arity,

    -- Now we generate the actual proof of the target.
    tgt ← target,
    proof ← mk_mapp inj_name (list.repeat none (inj_arity - 3) ++ [some h, some tgt]),
    eapply proof,
    intron_with num_equations ns base offset
  else do
    tgt ← target,
    let inductive_name := constructor_left.get_prefix,
    pr ← mk_app (inductive_name <.> "no_confusion") [tgt, lhs, rhs, h],
    exact pr,
    return ([], ns)

/--
Simplify the equation `h` using injectivity of constructors. See
`injection_with`. Returns the hypotheses that were added to the context, or an
empty list if the goal was solved by contradiction.
-/
meta def injection (h : expr) (base := `h) (offset := some 1)
  : tactic (list expr) :=
prod.fst <$> injection_with h [] base offset

private meta def injections_with_inner (base : name) (offset : option ℕ)
  : ℕ → list expr → list name → tactic unit
| 0     lc        ns := fail "recursion depth exceeded"
| (n+1) []        ns := skip
| (n+1) (h :: lc) ns := do
  o ← try_core (injection_with h ns base offset),
  match o with
  | none          := injections_with_inner (n+1) lc ns
  | some ([], _)  := skip -- This means that the contradiction part was triggered and the goal is done
  | some (t, ns') := injections_with_inner n (t ++ lc) ns'
  end

/--
Simplifies equations in the context using injectivity of constructors. For
each equation `h : C x₁ ... xₙ = D y₁ ... yₘ` in the context, where `C` and `D`
are constructors of the same data type, `injections_with` does the following:

- If `C = D`, it adds equations `x₁ = y₁`, ..., `xₙ = yₙ`.
- If `C ≠ D`, it solves the goal by contradiction.

See `injection_with` for details, including information about `base` and
`offset`.

`injections_with` also recurses into the new equations `xᵢ = yᵢ`. If it has to
recurse more than five times, it fails.
-/
meta def injections_with (ns : list name) (base := `h) (offset := some 1)
  : tactic unit :=
do lc ← local_context,
   injections_with_inner base offset 5 lc ns

end tactic
