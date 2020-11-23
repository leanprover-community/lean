class succeeds_w_cache (α : Type) := (a : α)
class fails_quickly_w_cache (α : Type) extends succeeds_w_cache α
class loops_wo_cache (α : Type) := (a : α)
class has_no_inst (α : Type)

instance loops_wo_cache.loop {α} [loops_wo_cache α] [inhabited α] :
    loops_wo_cache α :=
‹loops_wo_cache α›

instance inhabited.to_loops_wo_cache {α} [inhabited α] : loops_wo_cache α :=
{a := default _}

instance loops_wo_cache.to_fails_quickly_w_cache {α} [has_no_inst α] [loops_wo_cache α] :
    fails_quickly_w_cache α :=
{a := loops_wo_cache.a}

@[priority 1] instance inhabited.to_succeeds_w_cache {α} [inhabited α] :
    succeeds_w_cache α :=
{a := default _}

#check (by apply_instance : succeeds_w_cache ℕ)

open tactic
#eval do
x ← to_expr ``(succeeds_w_cache.a),
infer_type x >>= unify `(nat),
unify `(nat.zero) x
