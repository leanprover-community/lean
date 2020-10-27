open tactic local_context tactic.unsafe tactic.unsafe.type_context

run_cmd do
    n ← type_context.run (pure "hello type_context"),
    trace n

run_cmd do
    n ← type_context.run (do x ← pure "hello", pure x),
    trace n

run_cmd do
    n ← type_context.run $ (λ x, x) <$>  pure "hello",
    trace n

run_cmd do -- should fail
    f : ℕ ← type_context.run (type_context.fail $ "I failed"),
    trace f

run_cmd do
    m ← tactic.mk_meta_var `(nat),
    e ← pure $ `([4,3,2]),
    b ← type_context.run (type_context.unify m e),
    trace b, -- should be ff because the types are not equal
    type_context.run (is_assigned m) >>= trace -- should be ff


run_cmd do
    m ← tactic.mk_meta_var `(nat),
    r : nat ← type_context.run (do unify m `(4), type_context.failure) <|> pure 5,
    m ← instantiate_mvars m,
    trace m -- should be "?m_1"

/- What happens when you assign an mvar to itself?
   It shouldn't stop you but it shouldn't stack-overflow either. -/
run_cmd do -- should fail with a 'deep recursion'
  type ← tactic.to_expr ```(nat),
  m ← tactic.mk_meta_var type,
  a ← type_context.run (type_context.assign m m *> type_context.get_assignment m),
  trace $ to_bool $ a = m, -- should be tt
  instantiate_mvars m

run_cmd do -- should fail with a 'deep recursion'
  type ← tactic.to_expr ```(nat),
  m ← tactic.mk_meta_var type,
  m₂ ← to_expr ```(%%m + %%m),
  type_context.run (type_context.assign m m₂),
  instantiate_mvars m

/- What happens when you assign a pair of mvars to each other? -/
run_cmd do -- should fail with a 'deep recursion'
  type ← tactic.to_expr ```(nat),
  m₁ ← tactic.mk_meta_var type,
  m₂ ← tactic.mk_meta_var type,
  type_context.run (type_context.assign m₁ m₂),
  type_context.run (type_context.assign m₂ m₁),
  trace m₁,
  trace m₂

run_cmd do
    x : pexpr ← resolve_name `int.eq_neg_of_eq_neg,
    x ← to_expr x,
    y ← infer_type x,
    (t,us,es) ← type_context.run $ type_context.to_tmp_mvars y,
    trace t,
    trace us,
    trace es,
    tactic.apply `(trivial), set_goals []

/- Some examples of rewriting tactics using type_context. -/

meta def my_infer : expr → tactic expr
| e := type_context.run $ type_context.infer e

run_cmd  my_infer `(4 : nat) >>= tactic.trace

meta def my_intro_core : expr → type_context (expr × expr) | goal := do
    target ← infer goal,
    match target with
    |(expr.pi n bi y b) := do
        lctx ← get_context goal,
        some (h,lctx) ← pure $ local_context.mk_local n y bi lctx,
        b ← pure $ expr.instantiate_var b h,
        goal' ← mk_mvar name.anonymous b (some lctx),
        assign goal $ expr.lam n bi y $ expr.mk_delayed_abstraction goal' [expr.local_uniq_name h],
        pure (h, goal')
    |_ := type_context.failure
    end
open tactic

meta def my_intro : name → tactic expr | n := do
    goal :: rest ← get_goals,
    (h, goal') ← type_context.run $ my_intro_core goal,
    set_goals $ goal' :: rest,
    pure h

lemma my_intro_test : ∀ (x : ℕ), x = x := begin
  my_intro `hello,
  refl
end
#print my_intro_test
open native

meta instance level.has_lt : has_lt level := ⟨λ x y, level.lt x y⟩
meta instance level.dec_lt : decidable_rel (level.has_lt.lt) := by apply_instance

meta def my_mk_pattern (ls : list level) (es : list expr) (target : expr)
  (ous : list level) (os : list expr) : tactic pattern
:= type_context.run $ do
    (t, extra_ls, extra_es) ← type_context.to_tmp_mvars target,
    level2meta : list (name × level) ← ls.mfoldl (λ acc l, do
        match l with
        | level.param n :=
            pure $ (prod.mk n $ type_context.level.mk_tmp_mvar $ acc.length + extra_ls.length) :: acc
        | _ := type_context.failure end
    ) [],
    let convert_level := λ l, level.instantiate l level2meta,
    expr2meta : rb_map expr expr ← es.mfoldl (λ acc e, do
        e_type ← infer e,
        e_type ← pure $ expr.replace e_type (λ x _, rb_map.find acc x),
        e_type ← pure $ expr.instantiate_univ_params e_type level2meta,
        i ← pure $ rb_map.size acc + extra_es.length,
        m ← pure $ type_context.mk_tmp_mvar i e_type,
        pure $ rb_map.insert acc e m
    ) $ rb_map.mk _ _,
    let convert_expr := λ x, expr.instantiate_univ_params (expr.replace x (λ x _, rb_map.find expr2meta x)) level2meta,
    uoutput ← pure $ ous.map convert_level,
    output ← pure $ os.map convert_expr,
    t ← pure $ convert_expr target,
    pure $ tactic.pattern.mk t uoutput output (extra_ls.length + level2meta.length) (extra_es.length + expr2meta.size)

/-- Reimplementation of tactic.match_pattern -/
meta def my_match_pattern_core : tactic.pattern → expr → type_context (list level × list expr)
| ⟨target, uoutput, moutput, nuvars, nmvars⟩ e :=
    -- open a temporary metavariable scope.
    tmp_mode nuvars nmvars (do
        -- match target with e.
        result ← type_context.unify target e,
        if (¬ result) then type_context.fail "failed to unify" else do
        -- fail when a tmp is not assigned
        list.mmap (level.tmp_get_assignment) $ list.range nuvars,
        list.mmap (tmp_get_assignment) $ list.range nmvars,
        -- instantiate the temporary metavariables.
        uo ← list.mmap level.instantiate_mvars $ uoutput,
        mo ← list.mmap instantiate_mvars $ moutput,
        pure (uo, mo)
    )

meta def my_match_pattern : pattern → expr → tactic (list level × list expr)
|p e := do type_context.run $ my_match_pattern_core p e

/- Make a pattern for testing. -/
meta def my_pat := do
    T ← to_expr ```(Type),
    α ← pure $ expr.local_const `α `α binder_info.implicit T,
    h ← pure $ expr.local_const `h `h binder_info.default α,
    LT ← to_expr ```(list %%α),
    t ← pure $ expr.local_const `t `t binder_info.default LT,
    target ← to_expr ```(@list.cons %%α %%h %%t),
    my_mk_pattern [] [α,h,t] target [] [h,t]

run_cmd do
    p ← my_pat,
    trace $ p.target

run_cmd do -- ([], [3, [4, 5]])
    p ← my_pat,
    res ←  my_match_pattern p `([3,4,5]),
    tactic.trace res

run_cmd do -- should fail since doesn't match the pattern.
    p ← my_pat,
    e ← to_expr ```(list.empty),
    res ←  my_match_pattern p `([] : list ℕ),
    tactic.trace res

run_cmd do
    type_context.run (do
        lc0 ← type_context.get_local_context,
        type_context.push_local `hi `(nat),
        type_context.push_local `there `(nat),
        lc1 ← type_context.get_local_context,
        type_context.pop_local,
        lc2 ← type_context.get_local_context,
        type_context.trace lc0,
        type_context.trace lc1,
        type_context.trace lc2,
        pure ()
)

run_cmd do
    type_context.run (do
        hi ← mk_mvar `hi `(nat),
        some hello ← type_context.try (do
            type_context.is_declared hi >>= guardb,
            type_context.is_assigned hi >>= (guardb ∘ bnot),
            type_context.assign hi `(4),
            type_context.is_assigned hi >>= guardb,
            hello ← mk_mvar `hello `(nat),
            type_context.is_declared hello >>= guardb,
            pure hello
        ),
        type_context.is_declared hi >>= guardb,
        type_context.is_declared hello >>= guardb,
        pure ()
    )

run_cmd do
    type_context.run (do
        hi ← mk_mvar `hi `(nat),
        none : option unit ← type_context.try (do
            type_context.assign hi `(4),
            push_local `H `(nat),
            failure
        ),
        type_context.is_declared hi >>= guardb,
        type_context.is_assigned hi >>= (guardb ∘ bnot),
        -- [note] the local variable stack should escape the try block.
        type_context.get_local_context >>= (λ l, guardb $ not $ list.empty $ local_context.to_list $ l),
        pure ()
    )

-- tactic.get_fun_info and unsafe.type_context.get_fun_info should do the same thing.
run_cmd do
    f ← tactic.resolve_name `has_bind.and_then >>= pure ∘ pexpr.mk_explicit >>= to_expr,
    fi ← tactic.get_fun_info f,
    fi ← to_string <$> tactic.pp fi,
    fi₂ ← type_context.run (unsafe.type_context.get_fun_info f),
    fi₂ ← to_string <$> tactic.pp fi₂,
    guard (fi = fi₂)

open tactic.unsafe.type_context
-- in_tmp_mode should work
run_cmd do
    type_context.run (do
        in_tmp_mode >>= guardb ∘ bnot,
        type_context.tmp_mode 0 3 (do
            in_tmp_mode >>= guardb,
            tmp_mode 0 2 (do
                in_tmp_mode >>= guardb
            ),
            in_tmp_mode >>= guardb
        ),
        in_tmp_mode >>= guardb ∘ bnot
    )

#eval to_bool $ local_context.empty = local_context.empty

