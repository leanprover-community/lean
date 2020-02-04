open tactic expr

set_option pp.all true
set_option trace.check true

-- ?m_1  =?=  (λ x, ?m_1) unit.star
#eval do
m ← mk_meta_var `(Type),
let e :=
  (lam `x binder_info.default (const ``unit []) m)
    (const ``unit.star []),
is_def_eq m e


/-- similar to `mk_local_pis` but make meta variables instead of
    local constants -/
meta def mk_meta_pis : expr → tactic (list expr × expr)
| (expr.pi n bi d b) := do
  p ← mk_meta_var d,
  (ps, r) ← mk_meta_pis (expr.instantiate_var b p),
  return ((p :: ps), r)
| e := return ([], e)


-- The issue also occurs when instantiating some lemmas with metavariables
#eval do
c ← mk_const ``psigma.rev_lex_accessible.equations._eqn_1,
t ← infer_type c,
(ms, t') ← mk_meta_pis t,
type_check t'
