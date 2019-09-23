
universe u

-- set_option trace.type_context.is_def_eq_detail true

def x := 4
def y := 5

run_cmd (do
    -- let p : pexpr := ,
    pat ← tactic.pexpr_to_pattern
        ```(λ (α : Type) [group α] (a b : α), @has_mul.mul α _ a b),

    -- T : expr ← tactic.to_expr
    -- ([α,a,b,t], _) ← tactic.mk_local_pis T,

    e : expr ← tactic.to_expr ```(x * y),
    tactic.trace $ expr.get_app_fn e,
    tactic.trace $ pat.moutput,
    tactic.trace $ expr.get_app_fn pat.target,
    (us,ps) ←  tactic.match_pattern pat e tactic.transparency.none,
    tactic.trace ps

    -- fail
)

#eval "hello"

run_cmd tactic.has_attribute `simp `mul_assoc