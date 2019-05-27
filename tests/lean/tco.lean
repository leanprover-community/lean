open tco tactic

run_cmd do
    n ← tco.run (pure "hello tco"),
    trace n

run_cmd do
    n ← tco.run (do x ← pure "hello", pure x),
    trace n

run_cmd do -- should fail
    f : ℕ ← tco.run (tco.fail $ "I failed"),
    trace f

run_cmd do
    m ← tactic.mk_meta_var `(nat),
    e ← pure $ `([4,3,2]),
    b ← tco.run (tco.unify m e),
    trace b, -- should be ff because the types are not equal
    tco.run (is_assigned m) >>= trace -- should be ff


run_cmd do
    m ← tactic.mk_meta_var `(nat),
    r : nat ← tco.run (do tco.unify m `(4), tco.failure) <|> pure 5,
    m ← instantiate_mvars m,
    trace m -- should be "?m_1"

/- What happens when you assign an mvar to itself?
   It shouldn't stop you but it shouldn't stack-overflow either. -/
run_cmd do
  type ← tactic.to_expr ```(nat),
  m ← tactic.mk_meta_var type,
  a ← tco.run (tco.assign m m *> tco.get_assignment m),
  trace $ to_bool $ a = m, -- should be tt
  instantiate_mvars m

run_cmd do
  type ← tactic.to_expr ```(nat),
  m ← tactic.mk_meta_var type,
  m₂ ← to_expr ```(%%m + %%m),
  tco.run (tco.assign m m₂),
  instantiate_mvars m

/- What happens when you assign a pair of mvars to each other? -/
run_cmd do
  type ← tactic.to_expr ```(nat),
  m₁ ← tactic.mk_meta_var type,
  m₂ ← tactic.mk_meta_var type,
  tco.run (tco.assign m₁ m₂),
  tco.run (tco.assign m₂ m₁),
  trace m₁,
  trace m₂

/- Some examples of rewriting tactics using tco. -/

meta def my_infer : expr → tactic expr
| e := tco.run $ tco.infer e

run_cmd  my_infer `(4 : nat) >>= tactic.trace

meta def my_intro_core : expr → tco (expr × expr) | goal := do
    target ← infer goal,
    match target with
    |(expr.pi n bi y b) := do
        lctx ← get_context goal,
        some (h,lctx) ← pure $ lc.mk_local n y bi lctx,
        b ← pure $ expr.instantiate_var b h,
        goal' ← mk_mvar name.anonymous b lctx,
        assign goal $ expr.lam n bi y $ expr.mk_delayed_abstraction goal' [expr.local_uniq_name h],
        pure (h, goal')
    |_ := tco.failure
    end
open tactic

meta def my_intro : name → tactic expr | n := do
    goal :: rest ← get_goals,
    (h, goal') ← tco.run $ my_intro_core goal,
    set_goals $ goal' :: rest,
    pure h

lemma my_intro_test : ∀ (x : ℕ), x = x := begin
  my_intro `hello,
  refl
end
#print my_intro_test

/-- Reimplementation of tactic.match_pattern -/
meta def my_match_pattern_core : tactic.pattern → expr → tco (list level × list expr)
| ⟨target, uoutput, moutput, nuvars, nmvars⟩ e :=
    -- open a temporary metavariable scope.
    tmp_mode nuvars nmvars (do
        -- match target with e.
        result ← tco.unify target e,
        if (¬ result) then tco.fail "failed to unify" else do
        -- fail when a tmp is not assigned
        list.mmap (level.tmp_get_assignment) $ list.range nuvars,
        list.mmap (tmp_get_assignment) $ list.range nmvars,
        -- instantiate the temporary metavariables.
        uo ← list.mmap level.instantiate_mvars $ uoutput,
        mo ← list.mmap instantiate_mvars $ moutput,
        pure (uo, mo)
    )

meta def my_match_pattern : pattern → expr → tactic (list level × list expr)
|p e := do tco.run $ my_match_pattern_core p e

/- Make a pattern for testing. -/
meta def my_pat := do
    T ← to_expr ```(Type),
    α ← pure $ expr.local_const `α `α binder_info.implicit T,
    h ← pure $ expr.local_const `h `h binder_info.default α,
    LT ← to_expr ```(list %%α),
    t ← pure $ expr.local_const `t `t binder_info.default LT,
    target ← to_expr ```(@list.cons %%α %%h %%t),
    tactic.mk_pattern [] [α,h,t] target [] [h,t]

run_cmd do -- ([], [3, [4, 5]])
    p ← my_pat,
    res ←  my_match_pattern p `([3,4,5]),
    tactic.trace res

run_cmd do -- should fail since doesn't match the pattern.
    p ← my_pat,
    e ← to_expr ```(list.empty),
    res ←  my_match_pattern p `([] : list ℕ),
    tactic.trace res

