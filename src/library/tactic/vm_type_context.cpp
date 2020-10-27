/* Copyright 2019 E.W.Ayers */
#include "util/optional.h"
#include "util/name.h"
#include "library/type_context.h"
#include "library/tactic/tactic_state.h"
#include "library/vm/vm.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_name.h"
#include "library/tactic/fun_info_tactics.h"
#include "library/idx_metavar.h"
#include "library/tactic/vm_local_context.h"
#include "library/tactic/kabstract.h"

namespace lean {
/* [NOTE] this is a reference to a **mutable** type_context_old object.
The Lean user should never be able to access this object directly.
This is fine because it is only ever used as a hidden argumeent within the `tco` monad.
The `type_context` monad is implemented as `type_context_old & -> a ⊕ (unit -> format)`. */
struct vm_type_context_old : public vm_external {
    type_context_old & m_val;
    vm_type_context_old(type_context_old & v):m_val(v) {}
    virtual ~vm_type_context_old() {}
    virtual void dealloc() override { this->~vm_type_context_old(); get_vm_allocator().deallocate(sizeof(vm_type_context_old), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_type_context_old(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_type_context_old))) vm_type_context_old(m_val); }
    virtual unsigned int hash() { return 0; }
};
type_context_old & to_type_context_old(vm_obj const & o) {
    return static_cast<vm_type_context_old*>(to_external(o))->m_val;
}
static vm_obj mk_fail(vm_obj const & fmt) {return mk_vm_constructor(1, mk_vm_constant_format_thunk(fmt));}
static vm_obj mk_fail(format const & fmt) {return mk_fail(to_obj(fmt));}
static vm_obj mk_fail(char const * msg) {return mk_fail(format(msg));}
static vm_obj mk_fail(sstream const & strm) {return mk_fail(strm.str().c_str()); }
static vm_obj mk_succ(vm_obj const & o) {return mk_vm_constructor(0, o);}
static bool is_succ(vm_obj const & o) {return cidx(o) == 0;}
static vm_obj value(vm_obj const & o) {return cfield(o, 0);}
vm_obj tco_run (vm_obj const &, vm_obj const & tco, vm_obj const & t, vm_obj const & s0) {
    tactic_state s = tactic::to_state(s0);
    tactic_state_context_cache cache(s);
    type_context_old ctx = cache.mk_type_context(to_transparency_mode(t));
    vm_obj result = invoke(tco, mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_type_context_old))) vm_type_context_old(ctx)));
    if (is_succ(result)) {
        return tactic::mk_success(value(result), set_mctx(s, ctx.mctx()));
    } else {
        auto fmt_thunk = value(result);
        return tactic::mk_exception_from_format_thunk(fmt_thunk, s);
    }
}
vm_obj tco_infer (vm_obj const & e, vm_obj const & tco) {
    type_context_old & ctx = to_type_context_old(tco);
    expr x = to_expr(e);
    expr y = ctx.infer(x);
    return mk_succ(to_obj(y));
}
vm_obj tco_pure (vm_obj const &, vm_obj const & a, vm_obj const &) {
    return mk_succ(a);
}
vm_obj tco_bind (vm_obj const &, vm_obj const &, vm_obj const & x, vm_obj const & f, vm_obj const & tco) {
    vm_obj result = invoke(x, tco);
    if (is_succ(result)) {
        return invoke(f, value(result), tco);
    } else {
        return result;
    }
}
vm_obj tco_fail (vm_obj const & /* α */, vm_obj const & fmt, vm_obj const &) {
    return mk_fail(fmt);
}
vm_obj tco_get_context (vm_obj const & mvar, vm_obj const & c) {
    type_context_old & ctx = to_type_context_old(c);
    expr x = to_expr(mvar);
    if (!ctx.is_regular_mvar(x)) { return mk_fail(sstream() << "get_context failed: " << x << " is not a metavariable."); }
    local_context lc = ctx.mctx().get_metavar_decl(x).get_context();
    return mk_succ(to_obj(lc));
}
vm_obj tco_mk_mvar (vm_obj const & pp_n0, vm_obj const & y0, vm_obj const & l0, vm_obj const & c) {
    type_context_old & ctx = to_type_context_old(c);
    name pp_n = to_name(pp_n0);
    expr y = to_expr(y0);
    local_context l = is_none(l0) ? ctx.lctx() : to_local_context(get_some_value(l0));
    expr mv = ctx.mk_metavar_decl(pp_n, l, y);
    return mk_succ(to_obj(mv));
}
/* expr -> expr -> tco unit */
vm_obj tco_assign (vm_obj const & m0, vm_obj const & a0, vm_obj const & c) {
    type_context_old & ctx = to_type_context_old(c);
    expr m = to_expr(m0);
    expr a = to_expr(a0);
    if (!ctx.in_tmp_mode() && is_idx_metavar(m)) {return mk_fail(sstream() << "assign failed: not in temp mode and " << m << " is a tmp metavariable.");}
    if (!is_metavar(m)) {return mk_fail(sstream() << "assign failed: " << m << " is not a metavaraible."); }
    ctx.assign(m, a);
    return mk_succ(mk_vm_unit());
}
vm_obj tco_level_assign (vm_obj const & m0, vm_obj const & a0, vm_obj const & c) {
    type_context_old & ctx = to_type_context_old(c);
    level m = to_level(m0);
    level a = to_level(a0);
    if (!ctx.in_tmp_mode() && is_idx_metauniv(m)) {return mk_fail(sstream() << "level assign failed: not in temp mode and " << m << " is a tmp metavariable.");}
    if (!is_meta(m)) {return mk_fail(sstream() << "level assign failed: " << m << " is not a universe metavaraible."); }
    ctx.assign(m, a);
    return mk_succ(mk_vm_unit());
}
vm_obj tco_is_def_eq (vm_obj const & l0, vm_obj const & r0, vm_obj const & approx, vm_obj const & c0) {
    expr l = to_expr(l0);
    if (!closed(l)) {return mk_fail(sstream() << "is_def_eq failed: " << l << " contains de-Bruijn variables.");}
    expr r = to_expr(r0);
    if (!closed(r)) {return mk_fail(sstream() << "is_def_eq failed: " << r << " contains de-Bruijn variables.");}
    type_context_old & ctx = to_type_context_old(c0);
    type_context_old::approximate_scope scope(ctx, to_bool(approx));
    bool res = ctx.pure_is_def_eq(l, r);
    return mk_succ(mk_vm_bool(res));
}
vm_obj tco_unify (vm_obj const & l0, vm_obj const & r0, vm_obj const & approx, vm_obj const & c0) {
    expr l = to_expr(l0);
    if (!closed(l)) {return mk_fail(sstream() << "is_def_eq failed: " << l << " contains de-Bruijn variables.");}
    expr r = to_expr(r0);
    if (!closed(r)) {return mk_fail(sstream() << "is_def_eq failed: " << r << " contains de-Bruijn variables.");}
    type_context_old & ctx = to_type_context_old(c0);
    type_context_old::approximate_scope scope(ctx, to_bool(approx));
    bool res = ctx.is_def_eq(l, r);
    return mk_succ(mk_vm_bool(res));
}
/* type_context.tmp_mode : Π {α : Type}, ℕ → ℕ → type_context α → type_context α */
vm_obj tco_tmp_mode (vm_obj const &, vm_obj const & nu0, vm_obj const & nv0, vm_obj const & t0, vm_obj const & c0) {
    type_context_old & ctx = to_type_context_old(c0);
    type_context_old::tmp_mode_scope scope(ctx, to_unsigned(nu0), to_unsigned(nv0));
    auto res  = invoke(t0, c0);
    return res;
}
/* : Π {α : Type}, type_context α → type_context (option α)  */
vm_obj tco_try(vm_obj const &, vm_obj const & t0, vm_obj const & c0) {
    type_context_old & ctx = to_type_context_old(c0);
    ctx.push_scope();
    auto res = invoke(t0, c0);
    if (is_succ(res)) {
        ctx.commit_scope();
        return mk_succ(mk_vm_some(value(res)));
    } else {
        ctx.pop_scope();
        return mk_succ(mk_vm_none());
    }
}
vm_obj tco_in_tmp_mode (vm_obj const & c0) {
    type_context_old & ctx = to_type_context_old(c0);
    return mk_succ(mk_vm_bool(ctx.in_tmp_mode()));
}
vm_obj tco_instantiate_mvars (vm_obj const & e0, vm_obj const & c0) {
    type_context_old & ctx = to_type_context_old(c0);
    return mk_succ(to_obj(ctx.instantiate_mvars(to_expr(e0))));
}
vm_obj tco_level_instantiate_mvars (vm_obj const & l0, vm_obj const & c0) {
    type_context_old & ctx = to_type_context_old(c0);
    return mk_succ(to_obj(ctx.instantiate_mvars(to_level(l0))));
}
vm_obj tco_tmp_get_assignment (vm_obj const & i0, vm_obj const & c0) {
    type_context_old & ctx = to_type_context_old(c0);
    unsigned i = to_unsigned(i0);
    if (!ctx.in_tmp_mode()) {return mk_fail("tmp_get_assignment failed: not in tmp mode.");}
    optional<expr> o = ctx.get_tmp_mvar_assignment(i);
    if (!o) {
        return mk_fail(sstream() << "tmp_get_assignment failed: no assignment for " << i << " found");
    } else {
        return mk_succ(to_obj(*o));
    }
}
vm_obj tco_level_tmp_get_assignment (vm_obj const & i0, vm_obj const & c0) {
    type_context_old & ctx = to_type_context_old(c0);
    unsigned i = to_unsigned(i0);
    if (!ctx.in_tmp_mode()) {return mk_fail("level.tmp_get_assignment failed: not in tmp mode.");}
    optional<level> o = ctx.get_tmp_uvar_assignment(i);
    if (!o) {
        return mk_fail(sstream() << "level.tmp_get_assignment failed: no assignment for " << i << " found");
    } else {
        return mk_succ(to_obj(*o));
    }
}
vm_obj tco_is_tmp_mvar(vm_obj const & m0, vm_obj const & c0) {
    type_context_old & ctx = to_type_context_old(c0);
    return mk_succ(mk_vm_bool(ctx.is_tmp_mvar(to_expr(m0))));
}
vm_obj tco_is_regular_mvar(vm_obj const & m0, vm_obj const & c0) {
    type_context_old & ctx = to_type_context_old(c0);
    return mk_succ(mk_vm_bool(ctx.is_regular_mvar(to_expr(m0))));
}
vm_obj tco_is_assigned(vm_obj const & m0, vm_obj const & c0) {
    type_context_old & ctx = to_type_context_old(c0);
    return mk_succ(mk_vm_bool(ctx.is_assigned(to_expr(m0))));
}
vm_obj tco_get_assignment(vm_obj const & m0, vm_obj const & c0) {
    type_context_old & ctx = to_type_context_old(c0);
    expr m = to_expr(m0);
    optional<expr> a = ctx.get_assignment(m);
    if (a) {
        return mk_succ(to_obj(*a));
    } else {
        return mk_fail(sstream() << "Get assignment: no assignment exists for " << m);
    }
}
vm_obj tco_level_mk_tmp_mvar (vm_obj const & i0) {
    unsigned i = to_unsigned(i0);
    return to_obj(lean::mk_idx_metauniv(i));
}
vm_obj tco_mk_tmp_mvar (vm_obj const & i0, vm_obj const & type0) {
    unsigned i = to_unsigned(i0);
    expr y = to_expr(type0);
    return to_obj(lean::mk_idx_metavar(i, y));
}
vm_obj tco_to_tmp_mvars(vm_obj const & e0, vm_obj const & c0) {
        buffer<level> ls;
        buffer<expr>  es;
        type_context_old & ctx = to_type_context_old(c0);
        expr e = to_expr(e0);
        expr t = to_idx_metavars(ctx.mctx(), e, ls, es);
        return mk_succ(mk_vm_pair(to_obj(t), mk_vm_pair(to_obj(ls), to_obj(es))));
}
vm_obj tco_get_env(vm_obj const & c0) {
    return mk_succ(to_obj(to_type_context_old(c0).env()));
}
vm_obj tco_whnf(vm_obj const & e0, vm_obj const & c0) {
    return mk_succ(to_obj(to_type_context_old(c0).whnf(to_expr(e0))));
}
vm_obj tco_is_stuck(vm_obj const & e0, vm_obj const & c0) {
    return mk_succ(to_obj(to_type_context_old(c0).is_stuck(to_expr(e0))));
}
vm_obj tco_is_declared(vm_obj const & e0, vm_obj const & c0) {
    expr const & e = to_expr(e0);
    type_context_old & ctx = to_type_context_old(c0);
    return mk_succ(mk_vm_bool(
        (is_metavar_decl_ref(e) && ctx.mctx().find_metavar_decl(e))
        || (is_local_decl_ref(e) && ctx.lctx().find_local_decl(e))));
}
vm_obj tco_get_local_context(vm_obj const & c0) {
    return mk_succ(to_obj(to_type_context_old(c0).lctx()));
}
vm_obj tco_push_local(vm_obj const & n0, vm_obj const & t0, vm_obj const & bi0, vm_obj const & c0) {
    return mk_succ(to_obj(to_type_context_old(c0).push_local(to_name(n0), to_expr(t0), to_binder_info(bi0))));
}
vm_obj tco_pop_local(vm_obj const & c0) {
    type_context_old & ctx = to_type_context_old(c0);
    ctx.pop_local();
    return mk_succ(mk_vm_unit());
}
vm_obj tco_get_fun_info(vm_obj const & e0, vm_obj const & n0, vm_obj const & c0) {
    type_context_old & c = to_type_context_old(c0);
    try {
        if (is_none(n0)) {
            return mk_succ(to_obj(get_fun_info(c, to_expr(e0))));
        } else {
            return mk_succ(to_obj(get_fun_info(c, to_expr(e0), force_to_unsigned(get_some_value(n0), 0))));
        }
    } catch (exception const & ex) {
        return mk_fail("get_fun_info failed.");
    }
}
vm_obj tco_fold_mvars(vm_obj const &, vm_obj const & f0, vm_obj const & a0, vm_obj const & c0) {
    vm_obj r0 = mk_succ(a0);
    to_type_context_old(c0).mctx().for_each([&](metavar_decl const & d) {
        if (is_succ(r0)) {
            r0 = invoke(f0, value(r0), to_obj(d.mk_ref()), c0);
        }
    });
    return r0;
}

vm_obj tco_kdepends_on(vm_obj const & e, vm_obj const & t, vm_obj const & s) {
    try {
        type_context_old & ctx = to_type_context_old(s);
        return mk_succ(mk_vm_bool(kdepends_on(ctx, to_expr(e), to_expr(t))));
    } catch (exception & ex) {
        return mk_fail(ex.what());
    }
}

vm_obj tco_kabstract(vm_obj const & e, vm_obj const & t, vm_obj const & u, vm_obj const & s0) {
    try {
        type_context_old & ctx = to_type_context_old(s0);
        auto a = kabstract(ctx, to_expr(e), to_expr(t), occurrences(), to_bool(u));
        return mk_succ(to_obj(a));
    } catch (exception & ex) {
        return mk_fail(ex.what());
    }
}

void initialize_vm_type_context() {
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "pure"}), tco_pure);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "bind"}), tco_bind);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "fail"}), tco_fail);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "run"}), tco_run);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "infer"}), tco_infer);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "get_env"}), tco_get_env);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "get_context"}), tco_get_context);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "mk_mvar"}), tco_mk_mvar);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "fold_mvars"}), tco_fold_mvars);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "assign"}), tco_assign);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "level", "assign"}), tco_level_assign);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "unify"}), tco_unify);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "whnf"}), tco_whnf);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "is_stuck"}), tco_is_stuck);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "is_declared"}), tco_is_declared);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "get_local_context"}), tco_get_local_context);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "push_local"}), tco_push_local);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "pop_local"}), tco_pop_local);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "is_def_eq"}), tco_is_def_eq);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "tmp_mode"}), tco_tmp_mode);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "in_tmp_mode"}), tco_in_tmp_mode);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "instantiate_mvars"}), tco_instantiate_mvars);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "level",  "instantiate_mvars"}), tco_level_instantiate_mvars);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "tmp_get_assignment"}), tco_tmp_get_assignment);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "level",  "tmp_get_assignment"}), tco_level_tmp_get_assignment);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "is_tmp_mvar"}), tco_is_tmp_mvar);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "is_regular_mvar"}), tco_is_regular_mvar);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "is_assigned"}), tco_is_assigned);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "get_assignment"}), tco_get_assignment);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "level", "mk_tmp_mvar"}), tco_level_mk_tmp_mvar);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "mk_tmp_mvar"}), tco_mk_tmp_mvar);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "to_tmp_mvars"}), tco_to_tmp_mvars);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "get_fun_info"}), tco_get_fun_info);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "try"}), tco_try);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "kabstract"}), tco_kabstract);
    DECLARE_VM_BUILTIN(name({"tactic", "unsafe", "type_context", "kdepends_on"}), tco_kdepends_on);
}
void finalize_vm_type_context() {
}
}
