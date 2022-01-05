/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#define lean_simp_trace(CTX, N, CODE) lean_trace(N, scope_trace_env _scope1(CTX.env(), CTX); CODE)
#define lean_simp_trace_d(CTX, N, CODE) lean_trace_d(N, scope_trace_env _scope1(CTX.env(), CTX); CODE)

namespace lean {
template<typename Prover>
class instantiate_emetas_fn {
    Prover & m_prover;

    // TODO(Leo): move to a different module?
    optional<expr> try_auto_param(tmp_type_context & tmp_ctx, expr const & type) {
        optional<expr_pair> p = is_auto_param(type);
        if (!p) return none_expr();
        optional<name> c = name_lit_to_name(p->second);
        if (!c) return none_expr();
        optional<declaration> d = tmp_ctx.env().find(*c);
        if (!d) return none_expr();
        if (!tmp_ctx.is_def_eq(d->get_type(), mk_tactic_unit())) return none_expr();

        vm_obj tac = get_vm_state().get_constant(*c);
        tactic_state s  = mk_tactic_state_for(tmp_ctx.env(), tmp_ctx.ctx().get_options(), name("_simp_auto_param"), tmp_ctx.ctx().lctx(), p->first);
        vm_obj r_obj    = invoke(tac, to_obj(s));
        optional<tactic_state> s_new = tactic::is_success(r_obj);
        if (!s_new || s_new->goals()) return none_expr();
        metavar_context mctx   = s_new->mctx();
        expr result            = mctx.instantiate_mvars(s_new->main());
        if (has_expr_metavar(result)) return none_expr();
        tmp_ctx.ctx().set_mctx(mctx);
        return some_expr(result);
    }

    enum emeta_result {
        FAILED, // This metavariable is definitely not solvable.
        WAITING, // This metavariable might be solved, if other variables are solved.
        DONE, // This metavariable is already solved.
        PROGRESS, // This metavariable has been solved in the last iteration.
    };

    /*
     * \brief Try to solve the metavariable by unification, synthesizing instances or calling the prover.
     */
    emeta_result solve_emeta(tmp_type_context & tmp_ctx, expr const & mvar, bool const & is_instance) {
        unsigned mvar_idx = to_meta_idx(mvar);
        expr mvar_type = tmp_ctx.instantiate_mvars(tmp_ctx.infer(mvar));
        if (tmp_ctx.is_eassigned(mvar_idx)) return DONE;

        if (is_instance && tmp_ctx.ctx().ready_to_synthesize(mvar_type)) {
            // Use the *temporary* context for the instance search
            // in order to also fill in any previous temporary metas created by matching.
            if (auto v = tmp_ctx.mk_class_instance(mvar_type)) {
                if (!tmp_ctx.is_def_eq(mvar, *v)) {
                    lean_simp_trace(tmp_ctx, name({"simplify", "failure"}),
                                    tout() << "unable to assign instance for: " << mvar_type << "\n";);
                    return FAILED;
                } else {
                    return PROGRESS;
                }
            } else {
                lean_simp_trace(tmp_ctx, name({"simplify", "failure"}),
                                tout() << "unable to synthesize instance for: " << mvar_type << "\n";);
                return FAILED;
            }
        }
        if (tmp_ctx.is_eassigned(mvar_idx)) return DONE;

        // `mk_class_instance` can deal with temporary metavariables, but other tactics
        // (including `simp` itself when called recursively to solve goals) usually can't.
        if (has_idx_metavar(mvar_type)) {
            return WAITING;
        }

        if (optional<expr> pf = try_auto_param(tmp_ctx, mvar_type)) {
            lean_verify(tmp_ctx.is_def_eq(mvar, *pf));
            return PROGRESS;
        }

        if (tmp_ctx.ctx().is_prop(mvar_type)) {
            if (auto pf = m_prover(tmp_ctx, mvar_type)) {
                lean_verify(tmp_ctx.is_def_eq(mvar, *pf));
                return PROGRESS;
            } else {
                lean_simp_trace(tmp_ctx, name({"simplify", "failure"}),
                                tout() << "failed to prove: " << mvar << " : " << mvar_type << "\n";);
                return FAILED;
            }
        } else {
            // This variable can't be inferred by itself, but it might still be possible through unifying another variable.
            // (For example, as `out_param Type` to an instance that hasn't passed through `solve_emeta`;
            // such cases where the type is already known but the value isn't, won't be caught by the `has_idx_metavar` check above.)
            lean_simp_trace(tmp_ctx, name({"simplify", "failure"}),
                            tout() << "failed to assign: " << mvar << " : " << mvar_type << "\n";);
            return WAITING;
        }
    }

public:
    instantiate_emetas_fn(Prover & prover):
        m_prover(prover) {}

    bool operator()(tmp_type_context & tmp_ctx, list<expr> const & emetas, list<bool> const & instances) {
        // Repeat until we stop making progress or all variables are instantiated.
        bool any_progress = false;
        bool any_waiting = false;
        do {
            any_progress = false;
            any_waiting = false;
            bool any_failed = false; // Early exit if there's something definitively impossible to solve.
            for_each2(emetas, instances, [&](expr const & mvar, bool const & is_instance) {
                    if (any_failed) return;
                    switch (solve_emeta(tmp_ctx, mvar, is_instance)) {
                        case DONE: break;
                        case PROGRESS: any_progress = true; break;
                        case WAITING: any_waiting = true; break;
                        case FAILED: any_failed = true; break;
                    }
                });
            if (any_failed) {
                return false;
            }
        } while (any_progress && any_waiting);
        return !any_waiting;
    }
};
}
