/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.meta.tactic init.meta.attribute init.meta.constructor_tactic
import init.meta.relation_tactics init.meta.occurrences
import init.data.option.basic

open tactic

def simp.default_max_steps := 10000000

/-- Prefix the given `attr_name` with `"simp_attr"`. -/
meta constant mk_simp_attr_decl_name (attr_name : name) : name

/-- Simp lemmas are used by the "simplifier" family of tactics.
`simp_lemmas` is essentially a pair of tables `rb_map (expr_type × name) (priority_list simp_lemma)`.
One of the tables is for congruences and one is for everything else.
An individual simp lemma is:
- A kind which can be `Refl`, `Simp` or `Congr`.
- A pair of `expr`s `l ~> r`. The rb map is indexed by the name of `get_app_fn(l)`.
- A proof that `l = r` or `l ↔ r`.
- A list of the metavariables that must be filled before the proof can be applied.
- A priority number
-/
meta constant simp_lemmas : Type
/-- Make a new table of simp lemmas -/
meta constant simp_lemmas.mk : simp_lemmas
/-- Merge the simp_lemma tables. -/
meta constant simp_lemmas.join : simp_lemmas → simp_lemmas → simp_lemmas
/-- Remove the given lemmas from the table. Use the names of the lemmas. -/
meta constant simp_lemmas.erase : simp_lemmas → list name → simp_lemmas
/-- Makes the default simp_lemmas table which is composed of all lemmas tagged with `simp`. -/
meta constant simp_lemmas.mk_default : tactic simp_lemmas
/-- Add a simplification lemma by an expression `p`. Some conditions on `p` must hold for it to be added, see list below.
If your lemma is not being added, you can see the reasons by setting `set_option trace.simp_lemmas true`.

- `p` must have the type `Π (h₁ : _) ... (hₙ : _), LHS ~ RHS` for some reflexive, transitive relation (usually `=`).
- Any of the hypotheses `hᵢ` should either be present in `LHS` or otherwise a `Prop` or a typeclass instance.
- `LHS` should not occur within `RHS`.
- `LHS` should not occur within a hypothesis `hᵢ`.

 -/
meta constant simp_lemmas.add (s : simp_lemmas) (e : expr) (symm : bool := false) : tactic simp_lemmas
/-- Add a simplification lemma by it's declaration name. See `simp_lemmas.add` for more information.-/
meta constant simp_lemmas.add_simp (s : simp_lemmas) (id : name) (symm : bool := false) : tactic simp_lemmas
/-- Adds a congruence simp lemma to simp_lemmas.
A congruence simp lemma is a lemma that breaks the simplification down into separate problems.
For example, to simplify `a ∧ b` to `c ∧ d`, we should try to simp `a` to `c` and `b` to `d`.
For examples of congruence simp lemmas look for lemmas with the `@[congr]` attribute.
```lean
lemma if_simp_congr ... (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) : ite b x y = ite c u v := ...
lemma imp_congr_right (h : a → (b ↔ c)) : (a → b) ↔ (a → c) := ...
lemma and_congr (h₁ : a ↔ c) (h₂ : b ↔ d) : (a ∧ b) ↔ (c ∧ d) := ...
```
-/
meta constant simp_lemmas.add_congr : simp_lemmas → name → tactic simp_lemmas

/-- Add expressions to a set of simp lemmas using `simp_lemmas.add`.

  This is the new version of `simp_lemmas.append`,
  which also allows you to set the `symm` flag.
-/
meta def simp_lemmas.append_with_symm (s : simp_lemmas) (hs : list (expr × bool)) :
  tactic simp_lemmas :=
hs.mfoldl (λ s h, simp_lemmas.add s h.fst h.snd) s
/-- Add expressions to a set of simp lemmas using `simp_lemmas.add`.

  This is the backwards-compatibility version of `simp_lemmas.append_with_symm`,
  and sets all `symm` flags to `ff`.
-/
meta def simp_lemmas.append (s : simp_lemmas) (hs : list expr) : tactic simp_lemmas :=
hs.mfoldl (λ s h, simp_lemmas.add s h ff) s

/-- `simp_lemmas.rewrite s e prove R` apply a simplification lemma from 's'

   - 'e'     is the expression to be "simplified"
   - 'prove' is used to discharge proof obligations.
   - 'r'     is the equivalence relation being used (e.g., 'eq', 'iff')
   - 'md'    is the transparency; how aggresively should the simplifier perform reductions.

   Result (new_e, pr) is the new expression 'new_e' and a proof (pr : e R new_e) -/
meta constant simp_lemmas.rewrite (s : simp_lemmas) (e : expr)
                                  (prove : tactic unit := failed) (r : name := `eq) (md := reducible)
                                  : tactic (expr × expr)
meta constant simp_lemmas.rewrites (s : simp_lemmas) (e : expr)
                                  (prove : tactic unit := failed) (r : name := `eq) (md := reducible)
                                  : tactic $ list (expr × expr)
/-- `simp_lemmas.drewrite s e` tries to rewrite 'e' using only refl lemmas in 's' -/
meta constant simp_lemmas.drewrite (s : simp_lemmas) (e : expr) (md := reducible) : tactic expr

meta constant is_valid_simp_lemma_cnst : name → tactic bool
meta constant is_valid_simp_lemma : expr → tactic bool

meta constant simp_lemmas.pp : simp_lemmas → tactic format

meta instance : has_to_tactic_format simp_lemmas :=
⟨simp_lemmas.pp⟩

namespace tactic
/- Remark: `transform` should not change the target. -/
/-- Revert a local constant, change its type using `transform`.  -/
meta def revert_and_transform (transform : expr → tactic expr) (h : expr) : tactic unit :=
do num_reverted : ℕ ← revert h,
   t ← target,
   match t with
   | expr.pi n bi d b  :=
        do h_simp ← transform d,
           unsafe_change $ expr.pi n bi h_simp b
   | expr.elet n g e f :=
        do h_simp ← transform g,
           unsafe_change $ expr.elet n h_simp e f
   | _ := fail "reverting hypothesis created neither a pi nor an elet expr (unreachable?)"
   end,
   intron num_reverted

/-- `get_eqn_lemmas_for deps d` returns the automatically generated equational lemmas for definition d.
   If deps is tt, then lemmas for automatically generated auxiliary declarations used to define d are also included. -/
meta def get_eqn_lemmas_for (deps : bool) (d : name) : tactic (list name) := do
env ← get_env,
pure $ if deps then env.get_ext_eqn_lemmas_for d else env.get_eqn_lemmas_for d

structure dsimp_config :=
(md                        := reducible) -- reduction mode: how aggressively constants are replaced with their definitions.
(max_steps : nat           := simp.default_max_steps) -- The maximum number of steps allowed before failing.
(canonize_instances : bool := tt) -- See the documentation in `src/library/defeq_canonizer.h`
(single_pass : bool        := ff) -- Visit each subterm no more than once.
(fail_if_unchanged         := tt) -- Don't throw if dsimp didn't do anything.
(eta                       := tt) -- allow eta-equivalence: `(λ x, F $ x) ↝ F`
(zeta : bool               := tt) -- do zeta-reductions: `let x : a := b in c ↝ c[x/b]`.
(beta : bool               := tt) -- do beta-reductions: `(λ x, E) $ (y) ↝ E[x/y]`.
(proj : bool               := tt) -- reduce projections: `⟨a,b⟩.1 ↝ a`.
(iota : bool               := tt) -- reduce recursors for inductive datatypes: eg `nat.rec_on (succ n) Z R ↝ R n $ nat.rec_on n Z R`
(unfold_reducible          := ff) -- if tt, definitions with `reducible` transparency will be unfolded (delta-reduced)
(memoize                   := tt) -- Perform caching of dsimps of subterms.
end tactic

/-- (Definitional) Simplify the given expression using *only* reflexivity equality lemmas from the given set of lemmas.
   The resulting expression is definitionally equal to the input.

   The list `u` contains defintions to be delta-reduced, and projections to be reduced.-/
meta constant simp_lemmas.dsimplify (s : simp_lemmas) (u : list name := []) (e : expr) (cfg : tactic.dsimp_config := {}) : tactic expr

namespace tactic
/- Remark: the configuration parameters `cfg.md` and `cfg.eta` are ignored by this tactic. -/
meta constant dsimplify_core
  /- The user state type. -/
  {α : Type}
  /- Initial user data -/
  (a : α)
  /- (pre a e) is invoked before visiting the children of subterm 'e',
     if it succeeds the result (new_a, new_e, flag) where
       - 'new_a' is the new value for the user data
       - 'new_e' is a new expression that must be definitionally equal to 'e',
       - 'flag'  if tt 'new_e' children should be visited, and 'post' invoked. -/
  (pre             : α → expr → tactic (α × expr × bool))
  /- (post a e) is invoked after visiting the children of subterm 'e',
     The output is similar to (pre a e), but the 'flag' indicates whether
     the new expression should be revisited or not. -/
  (post            : α → expr → tactic (α × expr × bool))
  (e               : expr)
  (cfg             : dsimp_config := {})
  : tactic (α × expr)

meta def dsimplify
  (pre             : expr → tactic (expr × bool))
  (post            : expr → tactic (expr × bool))
  : expr → tactic expr :=
λ e, do (a, new_e) ← dsimplify_core ()
                       (λ u e, do r ← pre e, return (u, r))
                       (λ u e, do r ← post e, return (u, r)) e,
        return new_e

meta def get_simp_lemmas_or_default : option simp_lemmas → tactic simp_lemmas
| none     := simp_lemmas.mk_default
| (some s) := return s

meta def dsimp_target (s : option simp_lemmas := none) (u : list name := []) (cfg : dsimp_config := {}) : tactic unit :=
do
  s ← get_simp_lemmas_or_default s,
  t ← target >>= instantiate_mvars,
  s.dsimplify u t cfg >>= unsafe_change

meta def dsimp_hyp (h : expr) (s : option simp_lemmas := none) (u : list name := []) (cfg : dsimp_config := {}) : tactic unit :=
do s ← get_simp_lemmas_or_default s, revert_and_transform (λ e, s.dsimplify u e cfg) h

/- Remark: we use transparency.instances by default to make sure that we
   can unfold projections of type classes. Example:

          (@has_add.add nat nat.has_add a b)
-/

/-- Tries to unfold `e` if it is a constant or a constant application.
    Remark: this is not a recursive procedure. -/
meta constant dunfold_head (e : expr) (md := transparency.instances) : tactic expr

structure dunfold_config extends dsimp_config :=
(md := transparency.instances)

/- Remark: in principle, dunfold can be implemented on top of dsimp. We don't do it for
   performance reasons. -/

meta constant dunfold (cs : list name) (e : expr) (cfg : dunfold_config := {}) : tactic expr

meta def dunfold_target (cs : list name) (cfg : dunfold_config := {}) : tactic unit :=
do t ← target, dunfold cs t cfg >>= unsafe_change

meta def dunfold_hyp (cs : list name) (h : expr) (cfg : dunfold_config := {}) : tactic unit :=
revert_and_transform (λ e, dunfold cs e cfg) h

structure delta_config :=
(max_steps       := simp.default_max_steps)
(visit_instances := tt)

private meta def is_delta_target (e : expr) (cs : list name) : bool :=
cs.any (λ c,
  if e.is_app_of c then tt   /- Exact match -/
  else let f := e.get_app_fn in
       /- f is an auxiliary constant generated when compiling c -/
       f.is_constant && f.const_name.is_internal && (f.const_name.get_prefix = c))

/-- Delta reduce the given constant names -/
meta def delta (cs : list name) (e : expr) (cfg : delta_config := {}) : tactic expr :=
let unfold (u : unit) (e : expr) : tactic (unit × expr × bool) := do
  guard (is_delta_target e cs),
  (expr.const f_name f_lvls) ← return e.get_app_fn,
  env   ← get_env,
  decl  ← env.get f_name,
  new_f ← decl.instantiate_value_univ_params f_lvls,
  new_e ← head_beta (expr.mk_app new_f e.get_app_args),
  return (u, new_e, tt)
in do (c, new_e) ← dsimplify_core () (λ c e, failed) unfold e {max_steps := cfg.max_steps, canonize_instances := cfg.visit_instances},
      return new_e

meta def delta_target (cs : list name) (cfg : delta_config := {}) : tactic unit :=
do t ← target, delta cs t cfg >>= unsafe_change

meta def delta_hyp (cs : list name) (h : expr) (cfg : delta_config := {}) :tactic unit :=
revert_and_transform (λ e, delta cs e cfg) h

structure unfold_proj_config extends dsimp_config :=
(md := transparency.instances)

/-- If `e` is a projection application, try to unfold it, otherwise fail. -/
meta constant unfold_proj (e : expr) (md := transparency.instances) : tactic expr

meta def unfold_projs (e : expr) (cfg : unfold_proj_config := {}) : tactic expr :=
let unfold (changed : bool) (e : expr) : tactic (bool × expr × bool) := do
  new_e ← unfold_proj e cfg.md,
  return (tt, new_e, tt)
in do (tt, new_e) ← dsimplify_core ff (λ c e, failed) unfold e cfg.to_dsimp_config | fail "no projections to unfold",
      return new_e

meta def unfold_projs_target (cfg : unfold_proj_config := {}) : tactic unit :=
do t ← target, unfold_projs t cfg >>= unsafe_change

meta def unfold_projs_hyp (h : expr) (cfg : unfold_proj_config := {}) : tactic unit :=
revert_and_transform (λ e, unfold_projs e cfg) h

structure simp_config :=
(max_steps : nat           := simp.default_max_steps)
(contextual : bool         := ff)
(lift_eq : bool            := tt)
(canonize_instances : bool := tt)
(canonize_proofs : bool    := ff)
(use_axioms : bool         := tt)
(zeta : bool               := tt)
(beta : bool               := tt)
(eta  : bool               := tt)
(proj : bool               := tt) -- reduce projections
(iota : bool               := tt)
(iota_eqn : bool           := ff) -- reduce using all equation lemmas generated by equation/pattern-matching compiler
(constructor_eq : bool     := tt)
(single_pass : bool        := ff)
(fail_if_unchanged         := tt)
(memoize                   := tt)
(trace_lemmas              := ff)

/--
  `simplify s e cfg r prove` simplify `e` using `s` using bottom-up traversal.
  `discharger` is a tactic for dischaging new subgoals created by the simplifier.
   If it fails, the simplifier tries to discharge the subgoal by simplifying it to `true`.

   The parameter `to_unfold` specifies definitions that should be delta-reduced,
   and projection applications that should be unfolded.
-/
meta constant simplify (s : simp_lemmas) (to_unfold : list name := []) (e : expr) (cfg : simp_config := {}) (r : name := `eq)
                       (discharger : tactic unit := failed) : tactic (expr × expr × name_set)

meta def simp_target (s : simp_lemmas) (to_unfold : list name := []) (cfg : simp_config := {}) (discharger : tactic unit := failed) : tactic name_set :=
do t ← target >>= instantiate_mvars,
   (new_t, pr, lms) ← simplify s to_unfold t cfg `eq discharger,
   replace_target new_t pr,
   return lms

meta def simp_hyp (s : simp_lemmas) (to_unfold : list name := []) (h : expr) (cfg : simp_config := {}) (discharger : tactic unit := failed) : tactic (expr × name_set) :=
do when (expr.is_local_constant h = ff) (fail "tactic simp_at failed, the given expression is not a hypothesis"),
   htype ← infer_type h,
   (h_new_type, pr, lms) ← simplify s to_unfold htype cfg `eq discharger,
   new_hyp ← replace_hyp h h_new_type pr,
   return (new_hyp, lms)

/--
`ext_simplify_core a c s discharger pre post r e`:

- `a : α` - initial user data
- `c : simp_config` - simp configuration options
- `s : simp_lemmas` - the set of simp_lemmas to use. Remark: the simplification lemmas are not applied automatically like in the simplify tactic. The caller must use them at pre/post.
- `discharger : α → tactic α` - tactic for dischaging hypothesis in conditional rewriting rules. The argument 'α' is the current user data.
- `pre a s r p e` is invoked before visiting the children of subterm 'e'.
  + arguments:
    - `a` is the current user data
    - `s` is the updated set of lemmas if 'contextual' is `tt`,
    - `r` is the simplification relation being used,
    - `p` is the "parent" expression (if there is one).
    - `e` is the current subexpression in question.
  + if it succeeds the result is `(new_a, new_e, new_pr, flag)` where
    - `new_a` is the new value for the user data
    - `new_e` is a new expression s.t. `r e new_e`
    - `new_pr` is a proof for `r e new_e`, If it is none, the proof is assumed to be by reflexivity
    - `flag`  if tt `new_e` children should be visited, and `post` invoked.
- `(post a s r p e)` is invoked after visiting the children of subterm `e`,
  The output is similar to `(pre a r s p e)`, but the 'flag' indicates whether the new expression should be revisited or not.
- `r` is the simplification relation. Usually `=` or `↔`.
- `e` is the input expression to be simplified.

The method returns `(a,e,pr)` where

 - `a` is the final user data
 - `e` is the new expression
 - `pr` is the proof that the given expression equals the input expression.

Note that `ext_simplify_core` will succeed even if `pre` and `post` fail, as failures are used to indicate that the method should move on to the next subterm.
If it is desirable to propagate errors from `pre`, they can be propagated through the "user data".
An easy way to do this is to call `tactic.capture (do ...)` in the parts of `pre`/`post` where errors matter, and then use `tactic.unwrap a` on the result.

Additionally, `ext_simplify_core` does not propagate changes made to the tactic state by `pre` and `post.
If it is desirable to propagate changes to the tactic state in addition to errors, use `tactic.resume` instead of `tactic.unwrap`.
-/
meta constant ext_simplify_core
  {α : Type}
  (a : α)
  (c : simp_config)
  (s : simp_lemmas)
  (discharger : α → tactic α)
  (pre : α → simp_lemmas → name → option expr → expr → tactic (α × expr × option expr × bool))
  (post : α → simp_lemmas  → name → option expr → expr → tactic (α × expr × option expr × bool))
  (r : name) :
  expr → tactic (α × expr × expr)

private meta def is_equation : expr → bool
| (expr.pi n bi d b) := is_equation b
| e                  := match (expr.is_eq e) with (some a) := tt | none := ff end

meta def collect_ctx_simps : tactic (list expr) :=
local_context

section simp_intros

meta def intro1_aux : bool → list name → tactic expr
| ff _       := intro1
| tt (n::ns) := intro n
| _  _       := failed

structure simp_intros_config extends simp_config :=
(use_hyps := ff)

meta def simp_intros_aux (cfg : simp_config) (use_hyps : bool) (to_unfold : list name) : simp_lemmas → bool → list name → tactic simp_lemmas
| S tt     [] := try (simp_target S to_unfold cfg) >> return S
| S use_ns ns := do
  t ← target,
  if t.is_napp_of `not 1 then
    intro1_aux use_ns ns >> simp_intros_aux S use_ns ns.tail
  else if t.is_arrow then
    do {
      d ← return t.binding_domain,
      (new_d, h_d_eq_new_d, lms) ← simplify S to_unfold d cfg,
      h_d ← intro1_aux use_ns ns,
      h_new_d ← mk_eq_mp h_d_eq_new_d h_d,
      assertv_core h_d.local_pp_name new_d h_new_d,
      clear h_d,
      h_new   ← intro1,
      new_S ← if use_hyps then mcond (is_prop new_d) (S.add h_new ff) (return S)
              else return S,
      simp_intros_aux new_S use_ns ns.tail
    }
    <|>
    -- failed to simplify... we just introduce and continue
    (intro1_aux use_ns ns >> simp_intros_aux S use_ns ns.tail)
  else if t.is_pi || t.is_let then
    intro1_aux use_ns ns >> simp_intros_aux S use_ns ns.tail
  else do
    new_t ← whnf t reducible,
    if new_t.is_pi then unsafe_change new_t >> simp_intros_aux S use_ns ns
    else
      try (simp_target S to_unfold cfg) >>
      mcond (expr.is_pi <$> target)
        (simp_intros_aux S use_ns ns)
        (if use_ns ∧ ¬ns.empty then failed else return S)

meta def simp_intros (s : simp_lemmas) (to_unfold : list name := []) (ids : list name := []) (cfg : simp_intros_config := {}) : tactic unit :=
step $ simp_intros_aux cfg.to_simp_config cfg.use_hyps to_unfold s (bnot ids.empty) ids

end simp_intros

meta def mk_eq_simp_ext (simp_ext : expr → tactic (expr × expr)) : tactic unit :=
do (lhs, rhs)     ← target >>= match_eq,
   (new_rhs, heq) ← simp_ext lhs,
   unify rhs new_rhs,
   exact heq

/- Simp attribute support -/

meta def to_simp_lemmas : simp_lemmas → list name → tactic simp_lemmas
| S []      := return S
| S (n::ns) := do S' ← (has_attribute `congr n >> S.add_congr n) <|> S.add_simp n ff, to_simp_lemmas S' ns

meta def mk_simp_attr (attr_name : name) (attr_deps : list name := []) : command :=
do let t := `(user_attribute simp_lemmas),
   let v := `({name     := attr_name,
               descr    := "simplifier attribute",
               cache_cfg := {
                 mk_cache := λ ns, do {
                          s ← tactic.to_simp_lemmas simp_lemmas.mk ns,
                          s ← attr_deps.mfoldl
                                (λ s attr_name, do
                                   ns ← attribute.get_instances attr_name,
                                   to_simp_lemmas s ns)
                                s,
                          return s },
                 dependencies := `reducibility :: attr_deps}} : user_attribute simp_lemmas),
   let n := mk_simp_attr_decl_name attr_name,
   add_decl (declaration.defn n [] t v reducibility_hints.abbrev ff),
   attribute.register n
/--
### Example usage:
```lean
-- make a new simp attribute called "my_reduction"
run_cmd mk_simp_attr `my_reduction
-- Add "my_reduction" attributes to these if-reductions
attribute [my_reduction] if_pos if_neg dif_pos dif_neg

-- will return the simp_lemmas with the `my_reduction` attribute.
#eval get_user_simp_lemmas `my_reduction

```
 -/
meta def get_user_simp_lemmas (attr_name : name) : tactic simp_lemmas :=
if attr_name = `default then simp_lemmas.mk_default
else get_attribute_cache_dyn (mk_simp_attr_decl_name attr_name)

meta def join_user_simp_lemmas_core : simp_lemmas → list name → tactic simp_lemmas
| S []             := return S
| S (attr_name::R) := do S' ← get_user_simp_lemmas attr_name, join_user_simp_lemmas_core (S.join S') R

meta def join_user_simp_lemmas (no_dflt : bool) (attrs : list name) : tactic simp_lemmas :=
if no_dflt then
  join_user_simp_lemmas_core simp_lemmas.mk attrs
else do
  s ← simp_lemmas.mk_default,
  join_user_simp_lemmas_core s attrs

meta def simplify_top_down {α} (a : α) (pre : α → expr → tactic (α × expr × expr)) (e : expr) (cfg : simp_config := {}) : tactic (α × expr × expr) :=
ext_simplify_core a cfg simp_lemmas.mk (λ _, failed)
  (λ a _ _ _ e, do (new_a, new_e, pr) ← pre a e, guard (¬ new_e =ₐ e), return (new_a, new_e, some pr, tt))
  (λ _ _ _ _ _, failed)
  `eq e

meta def simp_top_down (pre : expr → tactic (expr × expr)) (cfg : simp_config := {}) : tactic unit :=
do t                   ← target,
   (_, new_target, pr) ← simplify_top_down () (λ _ e, do (new_e, pr) ← pre e, return ((), new_e, pr)) t cfg,
   replace_target new_target pr

meta def simplify_bottom_up {α} (a : α) (post : α → expr → tactic (α × expr × expr)) (e : expr) (cfg : simp_config := {}) : tactic (α × expr × expr) :=
ext_simplify_core a cfg simp_lemmas.mk (λ _, failed)
  (λ _ _ _ _ _, failed)
  (λ a _ _ _ e, do (new_a, new_e, pr) ← post a e, guard (¬ new_e =ₐ e), return (new_a, new_e, some pr, tt))
  `eq e

meta def simp_bottom_up (post : expr → tactic (expr × expr)) (cfg : simp_config := {}) : tactic unit :=
do t                   ← target,
   (_, new_target, pr) ← simplify_bottom_up () (λ _ e, do (new_e, pr) ← post e, return ((), new_e, pr)) t cfg,
   replace_target new_target pr

private meta def remove_deps (s : name_set) (h : expr) : name_set :=
if s.empty then s
else h.fold s (λ e o s, if e.is_local_constant then s.erase e.local_uniq_name else s)

/- Return the list of hypothesis that are propositions and do not have
   forward dependencies. -/
meta def non_dep_prop_hyps : tactic (list expr) :=
do
  ctx ← local_context,
  s   ← ctx.mfoldl (λ s h, do
           h_type ← infer_type h,
           let s := remove_deps s h_type,
           h_val  ← head_zeta h,
           let s := if h_val =ₐ h then s else remove_deps s h_val,
           mcond (is_prop h_type)
             (return $ s.insert h.local_uniq_name)
             (return s)) mk_name_set,
  t   ← target,
  let s := remove_deps s t,
  return $ ctx.filter (λ h, s.contains h.local_uniq_name)

section simp_all

meta structure simp_all_entry :=
(h        : expr) -- hypothesis
(new_type : expr) -- new type
(pr       : option expr) -- proof that type of h is equal to new_type
(s        : simp_lemmas) -- simplification lemmas for simplifying new_type

private meta def update_simp_lemmas (es : list simp_all_entry) (h : expr) : tactic (list simp_all_entry) :=
es.mmap $ λ e, do new_s ← e.s.add h ff, return {s := new_s, ..e}

/- Helper tactic for `init`.
   Remark: the following tactic is quadratic on the length of list expr (the list of non dependent propositions).
   We can make it more efficient as soon as we have an efficient simp_lemmas.erase. -/
private meta def init_aux : list expr → simp_lemmas → list simp_all_entry → tactic (simp_lemmas × list simp_all_entry)
| []      s r := return (s, r)
| (h::hs) s r := do
  new_r  ← update_simp_lemmas r h,
  new_s  ← s.add h ff,
  h_type ← infer_type h,
  init_aux hs new_s (⟨h, h_type, none, s⟩::new_r)

private meta def init (s : simp_lemmas) (hs : list expr) : tactic (simp_lemmas × list simp_all_entry) :=
init_aux hs s []

private meta def add_new_hyps (es : list simp_all_entry) : tactic unit :=
es.mmap' $ λ e,
   match e.pr with
   | none    := return ()
   | some pr :=
      assert e.h.local_pp_name e.new_type >>
      mk_eq_mp pr e.h >>= exact
   end

private meta def clear_old_hyps (es : list simp_all_entry) : tactic unit :=
es.mmap' $ λ e, when (e.pr ≠ none) (try (clear e.h))

private meta def join_pr : option expr → expr → tactic expr
| none       pr₂ := return pr₂
| (some pr₁) pr₂ := mk_eq_trans pr₁ pr₂

private meta def loop (cfg : simp_config) (discharger : tactic unit) (to_unfold : list name)
                      : list simp_all_entry → list simp_all_entry → simp_lemmas → bool → tactic name_set
| []      r  s m :=
  if m then loop r [] s ff
  else do
    add_new_hyps r,
    (lms, target_changed) ← (simp_target s to_unfold cfg discharger >>= λ ns, return (ns, tt)) <|>
                            (return (mk_name_set, ff)),
    guard (cfg.fail_if_unchanged = ff ∨ target_changed ∨ r.any (λ e, e.pr ≠ none)) <|> fail "simp_all tactic failed to simplify",
    clear_old_hyps r,
    return lms
| (e::es) r  s m := do
   let ⟨h, h_type, h_pr, s'⟩ := e,
   (new_h_type, new_pr, lms) ← simplify s' to_unfold h_type {fail_if_unchanged := ff, ..cfg} `eq discharger,
   if h_type =ₐ new_h_type then do
     new_lms ← loop es (e::r) s m,
     return (new_lms.fold lms (λ n ns, name_set.insert ns n))
   else do
     new_pr      ← join_pr h_pr new_pr,
     new_fact_pr ← mk_eq_mp new_pr h,
     if new_h_type = `(false) then do
       tgt         ← target,
       to_expr ``(@false.rec %%tgt %%new_fact_pr) >>= exact,
       return (mk_name_set)
     else do
       h0_type     ← infer_type h,
       let new_fact_pr := mk_id_proof new_h_type new_fact_pr,
       new_es      ← update_simp_lemmas es new_fact_pr,
       new_r       ← update_simp_lemmas r new_fact_pr,
       let new_r := {new_type := new_h_type, pr := new_pr, ..e} :: new_r,
       new_s       ← s.add new_fact_pr ff,
       new_lms ← loop new_es new_r new_s tt,
       return (new_lms.fold lms (λ n ns, name_set.insert ns n))

meta def simp_all (s : simp_lemmas) (to_unfold : list name) (cfg : simp_config := {}) (discharger : tactic unit := failed) : tactic name_set :=
do hs      ← non_dep_prop_hyps,
   (s, es) ← init s hs,
   loop cfg discharger to_unfold es [] s ff

end simp_all

/- debugging support for algebraic normalizer -/

meta constant trace_algebra_info : expr → tactic unit

end tactic

export tactic (mk_simp_attr)

run_cmd mk_simp_attr `norm [`simp]
