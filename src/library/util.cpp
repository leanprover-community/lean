/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "util/fresh_name.h"
#include "kernel/find_fn.h"
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "kernel/error_msgs.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/abstract_type_context.h"
#include "kernel/inductive/inductive.h"
#include "library/locals.h"
#include "library/util.h"
#include "library/annotation.h"
#include "library/constants.h"
#include "library/unfold_macros.h"
#include "library/pp_options.h"
#include "library/projection.h"
#include "library/replace_visitor.h"
#include "library/type_context.h"
#include "library/string.h"
#include "version.h"
#include "githash.h" // NOLINT

namespace lean {
name mk_unused_name(environment const & env, name const & n, unsigned & idx) {
    name curr = n;
    while (true) {
        if (!env.find(curr))
            return curr;
        curr = n.append_after(idx);
        idx++;
    }
}

name mk_unused_name(environment const & env, name const & n) {
    unsigned idx = 1;
    return mk_unused_name(env, n, idx);
}

/** \brief Return the "arity" of the given type. The arity is the number of nested pi-expressions. */
unsigned get_arity(expr type) {
    unsigned r = 0;
    while (is_pi(type)) {
        type = binding_body(type);
        r++;
    }
    return r;
}

optional<expr> is_optional_param(expr const & e) {
    if (is_app_of(e, get_opt_param_name(), 2)) {
        return some_expr(app_arg(e));
    } else {
        return none_expr();
    }
}

optional<expr_pair> is_auto_param(expr const & e) {
    if (is_app_of(e, get_auto_param_name(), 2)) {
        return optional<expr_pair>(app_arg(app_fn(e)), app_arg(e));
    } else {
        return optional<expr_pair>();
    }
}

level get_level(abstract_type_context & ctx, expr const & A) {
    expr S = ctx.relaxed_whnf(ctx.infer(A));
    if (!is_sort(S))
        throw exception("invalid expression, sort expected");
    return sort_level(S);
}

name mk_fresh_lp_name(level_param_names const & lp_names) {
    name l("l");
    int i = 1;
    while (std::find(lp_names.begin(), lp_names.end(), l) != lp_names.end()) {
        l = name("l").append_after(i);
        i++;
    }
    return l;
}

bool occurs(expr const & n, expr const & m) {
    return static_cast<bool>(find(m, [&](expr const & e, unsigned) { return n == e; }));
}

bool occurs(name const & n, expr const & m) {
    return static_cast<bool>(find(m, [&](expr const & e, unsigned) { return is_constant(e) && const_name(e) == n; }));
}

bool is_app_of(expr const & t, name const & f_name) {
    expr const & fn = get_app_fn(t);
    return is_constant(fn) && const_name(fn) == f_name;
}

bool is_app_of(expr const & t, name const & f_name, unsigned nargs) {
    expr const & fn = get_app_fn(t);
    return is_constant(fn) && const_name(fn) == f_name && get_app_num_args(t) == nargs;
}

expr consume_auto_opt_param(expr const & type) {
    if (is_app_of(type, get_auto_param_name(), 2) || is_app_of(type, get_opt_param_name(), 2)) {
        return app_arg(app_fn(type));
    } else {
        return type;
    }
}

optional<expr> unfold_term(environment const & env, expr const & e) {
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return none_expr();
    auto decl = env.find(const_name(f));
    if (!decl || !decl->is_definition())
        return none_expr();
    expr d = instantiate_value_univ_params(*decl, const_levels(f));
    buffer<expr> args;
    get_app_rev_args(e, args);
    return some_expr(apply_beta(d, args.size(), args.data()));
}

optional<expr> unfold_app(environment const & env, expr const & e) {
    if (!is_app(e))
        return none_expr();
    return unfold_term(env, e);
}

optional<level> dec_level(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::Meta:
        return none_level();
    case level_kind::Succ:
        return some_level(succ_of(l));
    case level_kind::Max:
        if (auto lhs = dec_level(max_lhs(l))) {
        if (auto rhs = dec_level(max_rhs(l))) {
            return some_level(mk_max(*lhs, *rhs));
        }}
        return none_level();
    case level_kind::IMax:
        // Remark: the following mk_max is not a typo. The following
        // assertion justifies it.
        if (auto lhs = dec_level(imax_lhs(l))) {
        if (auto rhs = dec_level(imax_rhs(l))) {
            return some_level(mk_max(*lhs, *rhs));
        }}
        return none_level();
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

/** \brief Return true if environment has a constructor named \c c that returns
    an element of the inductive datatype named \c I, and \c c must have \c nparams parameters. */
bool has_constructor(environment const & env, name const & c, name const & I, unsigned nparams) {
    auto d = env.find(c);
    if (!d || d->is_definition())
        return false;
    expr type = d->get_type();
    unsigned i = 0;
    while (is_pi(type)) {
        i++;
        type = binding_body(type);
    }
    if (i != nparams)
        return false;
    type = get_app_fn(type);
    return is_constant(type) && const_name(type) == I;
}

bool has_punit_decls(environment const & env) {
    return has_constructor(env, get_punit_star_name(), get_punit_name(), 0);
}

bool has_eq_decls(environment const & env) {
    return has_constructor(env, get_eq_refl_name(), get_eq_name(), 2);
}

bool has_heq_decls(environment const & env) {
    return has_constructor(env, get_heq_refl_name(), get_heq_name(), 2);
}

bool has_pprod_decls(environment const & env) {
    return has_constructor(env, get_pprod_mk_name(), get_pprod_name(), 4);
}

bool has_and_decls(environment const & env) {
    return has_constructor(env, get_and_intro_name(), get_and_name(), 4);
}

/* n is considered to be recursive if it is an inductive datatype and
   1) It has a constructor that takes n as an argument
   2) It is part of a mutually recursive declaration, and some constructor
      of an inductive datatype takes another inductive datatype from the
      same declaration as an argument. */
bool is_recursive_datatype(environment const & env, name const & n) {
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(env, n);
    if (!decl) return false;
    for (inductive::intro_rule const & intro : decl->m_intro_rules) {
        expr type = inductive::intro_rule_type(intro);
        while (is_pi(type)) {
            if (find(binding_domain(type), [&](expr const & e, unsigned) {
                        if (is_constant(e)) {
                            name const & c = const_name(e);
                            if (decl->m_name == c) return true;
                        }
                        return false;
                    })) {
                return true;
            }
            type = binding_body(type);
        }
    }
    return false;
}

bool is_reflexive_datatype(abstract_type_context & tc, name const & n) {
    environment const & env = tc.env();
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(env, n);
    if (!decl) return false;
    for (inductive::intro_rule const & intro : decl->m_intro_rules) {
        expr type = inductive::intro_rule_type(intro);
        while (is_pi(type)) {
            expr arg   = tc.whnf(binding_domain(type));
            if (is_pi(arg) && find(arg, [&](expr const & e, unsigned) { return is_constant(e) && const_name(e) == n; })) {
                return true;
            }
            expr local = mk_local(tc.next_name(), binding_domain(type));
            type = instantiate(binding_body(type), local);
        }
    }
    return false;
}

level get_datatype_level(environment const & env, expr const & ind_type) {
    expr it = ind_type;
    while (is_pi(it))
        it = binding_body(it);
    if (is_sort(it)) {
        return sort_level(it);
    } else {
        type_checker ctx(env);
        buffer<expr> telescope;
        expr it = ctx.whnf(to_telescope(ctx, ind_type, telescope));
        if (is_sort(it)) {
            return sort_level(it);
        } else {
            throw exception("invalid inductive datatype type");
        }
    }
}

expr update_result_sort(expr t, level const & l) {
    if (is_pi(t)) {
        return update_binding(t, binding_domain(t), update_result_sort(binding_body(t), l));
    } else if (is_sort(t)) {
        return update_sort(t, l);
    } else {
        lean_unreachable();
    }
}

bool is_inductive_predicate(environment const & env, name const & n) {
    if (!inductive::is_inductive_decl(env, n))
        return false; // n is not inductive datatype
    return is_zero(get_datatype_level(env, env.get(n).get_type()));
}

bool can_elim_to_type(environment const & env, name const & n) {
    if (!inductive::is_inductive_decl(env, n))
        return false; // n is not inductive datatype
    declaration ind_decl = env.get(n);
    declaration rec_decl = env.get(inductive::get_elim_name(n));
    return rec_decl.get_num_univ_params() > ind_decl.get_num_univ_params();
}

void get_intro_rule_names(environment const & env, name const & n, buffer<name> & result) {
    if (auto decl = inductive::is_inductive_decl(env, n)) {
        for (inductive::intro_rule const & ir : decl->m_intro_rules) {
            result.push_back(inductive::intro_rule_name(ir));
        }
    }
}

optional<name> is_constructor_app(environment const & env, expr const & e) {
    expr const & fn = get_app_fn(e);
    if (is_constant(fn))
        if (auto I = inductive::is_intro_rule(env, const_name(fn)))
            return optional<name>(const_name(fn));
    return optional<name>();
}

optional<name> is_constructor_app_ext(environment const & env, expr const & e) {
    if (auto r = is_constructor_app(env, e))
        return r;
    expr const & f = get_app_fn(e);
    if (!is_constant(f))
        return optional<name>();
    auto decl = env.find(const_name(f));
    if (!decl || !decl->is_definition())
        return optional<name>();
    expr const * it = &decl->get_value();
    while (is_lambda(*it))
        it = &binding_body(*it);
    return is_constructor_app_ext(env, *it);
}

static bool is_irrelevant_field_type(type_checker & tc, expr const & ftype) {
    if (tc.is_prop(ftype)) return true;
    buffer<expr> tele;
    expr n_ftype = to_telescope(tc, ftype, tele);
    return is_sort(n_ftype) || tc.is_prop(n_ftype);
}

void get_constructor_relevant_fields(environment const & env, name const & n, buffer<bool> & result) {
    lean_assert(inductive::is_intro_rule(env, n));
    expr type        = env.get(n).get_type();
    name I_name      = *inductive::is_intro_rule(env, n);
    unsigned nparams = *inductive::get_num_params(env, I_name);
    buffer<expr> telescope;
    type_checker tc(env);
    to_telescope(tc, type, telescope);
    lean_assert(telescope.size() >= nparams);
    for (unsigned i = nparams; i < telescope.size(); i++) {
        result.push_back(!is_irrelevant_field_type(tc, mlocal_type(telescope[i])));
    }
}

unsigned get_constructor_idx(environment const & env, name const & n) {
    lean_assert(inductive::is_intro_rule(env, n));
    name I_name = *inductive::is_intro_rule(env, n);
    buffer<name> cnames;
    get_intro_rule_names(env, I_name, cnames);
    unsigned r  = 0;
    for (name const & cname : cnames) {
        if (cname == n)
            return r;
        r++;
    }
    lean_unreachable();
}

unsigned get_num_inductive_hypotheses_for(environment const & env, name const & n, buffer<bool> & rec_mask) {
    lean_assert(inductive::is_intro_rule(env, n));
    lean_assert(rec_mask.empty());
    name I_name = *inductive::is_intro_rule(env, n);
    inductive::inductive_decl decl = *inductive::is_inductive_decl(env, I_name);
    type_context_old tc(env);
    type_context_old::tmp_locals locals(tc);
    expr type   = tc.whnf(env.get(n).get_type());
    unsigned r  = 0;
    while (is_pi(type)) {
        auto dom = tc.whnf(binding_domain(type));
        while (is_pi(dom)) {
            dom = tc.whnf(instantiate(binding_body(dom), locals.push_local_from_binding(dom)));
        }
        auto fn = get_app_fn(dom);
        if (is_constant(fn) && const_name(fn) == decl.m_name) {
            rec_mask.push_back(true);
            r++;
        } else {
            rec_mask.push_back(false);
        }
        type = tc.whnf(instantiate(binding_body(type), locals.push_local_from_binding(type)));
    }
    return r;
}

unsigned get_num_inductive_hypotheses_for(environment const & env, name const & n) {
    buffer<bool> rec_mask;
    return get_num_inductive_hypotheses_for(env, n, rec_mask);
}

void get_constructor_rec_arg_mask(environment const & env, name const & n, buffer<bool> & rec_mask) {
    get_num_inductive_hypotheses_for(env, n, rec_mask);
}

expr instantiate_univ_param (expr const & e, name const & p, level const & l) {
    return instantiate_univ_params(e, to_list(p), to_list(l));
}

unsigned get_expect_num_args(abstract_type_context & ctx, expr e) {
    push_local_fn push_local(ctx);
    unsigned r = 0;
    while (true) {
        e = ctx.whnf(e);
        if (!is_pi(e))
            return r;
        // TODO(Leo): try to avoid the following instantiate.
        expr local = push_local(binding_name(e), binding_domain(e), binding_info(e));
        e = instantiate(binding_body(e), local);
        r++;
    }
}

expr to_telescope(bool pi, expr e, buffer<expr> & telescope,
                  optional<binder_info> const & binfo) {
    while ((pi && is_pi(e)) || (!pi && is_lambda(e))) {
        expr local;
        if (binfo)
            local = mk_local(mk_fresh_name(), binding_name(e), binding_domain(e), *binfo);
        else
            local = mk_local(mk_fresh_name(), binding_name(e), binding_domain(e), binding_info(e));
        telescope.push_back(local);
        e = instantiate(binding_body(e), local);
    }
    return e;
}

expr to_telescope(expr const & type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    return to_telescope(true, type, telescope, binfo);
}

expr fun_to_telescope(expr const & e, buffer<expr> & telescope,
                      optional<binder_info> const & binfo) {
    return to_telescope(false, e, telescope, binfo);
}

expr to_telescope(type_checker & ctx, expr type, buffer<expr> & telescope, optional<binder_info> const & binfo) {
    expr new_type = ctx.whnf(type);
    while (is_pi(new_type)) {
        type = new_type;
        expr local;
        if (binfo)
            local = mk_local(ctx.next_name(), binding_name(type), binding_domain(type), *binfo);
        else
            local = mk_local(ctx.next_name(), binding_name(type), binding_domain(type), binding_info(type));
        telescope.push_back(local);
        type     = instantiate(binding_body(type), local);
        new_type = ctx.whnf(type);
    }
    return type;
}

/* ----------------------------------------------

   Helper functions for creating basic operations

   ---------------------------------------------- */
static expr * g_true = nullptr;
static expr * g_true_intro = nullptr;
static expr * g_and = nullptr;
static expr * g_and_intro = nullptr;
static expr * g_and_elim_left = nullptr;
static expr * g_and_elim_right = nullptr;

expr mk_true() {
    return *g_true;
}

bool is_true(expr const & e) {
    return e == *g_true;
}

expr mk_true_intro() {
    return *g_true_intro;
}

bool is_and(expr const & e) {
    return is_app_of(e, get_and_name(), 2);
}

bool is_and(expr const & e, expr & arg1, expr & arg2) {
    if (is_and(e)) {
        arg1 = app_arg(app_fn(e));
        arg2 = app_arg(e);
        return true;
    } else {
        return false;
    }
}

expr mk_and(expr const & a, expr const & b) {
    return mk_app(*g_and, a, b);
}

expr mk_and_intro(abstract_type_context & ctx, expr const & Ha, expr const & Hb) {
    return mk_app(*g_and_intro, ctx.infer(Ha), ctx.infer(Hb), Ha, Hb);
}

expr mk_and_elim_left(abstract_type_context & ctx, expr const & H) {
    expr a_and_b = ctx.whnf(ctx.infer(H));
    return mk_app(*g_and_elim_left, app_arg(app_fn(a_and_b)), app_arg(a_and_b), H);
}

expr mk_and_elim_right(abstract_type_context & ctx, expr const & H) {
    expr a_and_b = ctx.whnf(ctx.infer(H));
    return mk_app(*g_and_elim_right, app_arg(app_fn(a_and_b)), app_arg(a_and_b), H);
}

expr mk_unit(level const & l) {
    return mk_constant(get_punit_name(), {l});
}

expr mk_unit_mk(level const & l) {
    return mk_constant(get_punit_star_name(), {l});
}

expr mk_pprod(abstract_type_context & ctx, expr const & A, expr const & B) {
    level l1 = get_level(ctx, A);
    level l2 = get_level(ctx, B);
    return mk_app(mk_constant(get_pprod_name(), {l1, l2}), A, B);
}

expr mk_pprod_mk(abstract_type_context & ctx, expr const & a, expr const & b) {
    expr A = ctx.infer(a);
    expr B = ctx.infer(b);
    level l1 = get_level(ctx, A);
    level l2 = get_level(ctx, B);
    return mk_app(mk_constant(get_pprod_mk_name(), {l1, l2}), A, B, a, b);
}

expr mk_pprod_fst(abstract_type_context & ctx, expr const & p) {
    expr AxB = ctx.whnf(ctx.infer(p));
    expr const & A = app_arg(app_fn(AxB));
    expr const & B = app_arg(AxB);
    return mk_app(mk_constant(get_pprod_fst_name(), const_levels(get_app_fn(AxB))), A, B, p);
}

expr mk_pprod_snd(abstract_type_context & ctx, expr const & p) {
    expr AxB = ctx.whnf(ctx.infer(p));
    expr const & A = app_arg(app_fn(AxB));
    expr const & B = app_arg(AxB);
    return mk_app(mk_constant(get_pprod_snd_name(), const_levels(get_app_fn(AxB))), A, B, p);
}

static expr * g_nat         = nullptr;
static expr * g_nat_zero    = nullptr;
static expr * g_nat_one     = nullptr;
static expr * g_nat_bit0_fn = nullptr;
static expr * g_nat_bit1_fn = nullptr;
static expr * g_nat_add_fn  = nullptr;

static void initialize_nat() {
    g_nat            = new expr(mk_constant(get_nat_name()));
    g_nat_zero       = new expr(mk_app(mk_constant(get_has_zero_zero_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_zero_name())}));
    g_nat_one        = new expr(mk_app(mk_constant(get_has_one_one_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_one_name())}));
    g_nat_bit0_fn    = new expr(mk_app(mk_constant(get_bit0_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_add_name())}));
    g_nat_bit1_fn    = new expr(mk_app(mk_constant(get_bit1_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_one_name()), mk_constant(get_nat_has_add_name())}));
    g_nat_add_fn     = new expr(mk_app(mk_constant(get_has_add_add_name(), {mk_level_zero()}), {*g_nat, mk_constant(get_nat_has_add_name())}));
}

static void finalize_nat() {
    delete g_nat;
    delete g_nat_zero;
    delete g_nat_one;
    delete g_nat_bit0_fn;
    delete g_nat_bit1_fn;
    delete g_nat_add_fn;
}

expr mk_nat_type() { return *g_nat; }
bool is_nat_type(expr const & e) { return e == *g_nat; }
expr mk_nat_zero() { return *g_nat_zero; }
expr mk_nat_one() { return *g_nat_one; }
expr mk_nat_bit0(expr const & e) { return mk_app(*g_nat_bit0_fn, e); }
expr mk_nat_bit1(expr const & e) { return mk_app(*g_nat_bit1_fn, e); }
expr mk_nat_add(expr const & e1, expr const & e2) { return mk_app(*g_nat_add_fn, e1, e2); }

static expr * g_int = nullptr;

static void initialize_int() {
    g_int = new expr(mk_constant(get_int_name()));
}

static void finalize_int() {
    delete g_int;
}

expr mk_int_type() { return *g_int; }
bool is_int_type(expr const & e) { return e == *g_int; }

static expr * g_char = nullptr;

expr mk_char_type() { return *g_char; }

static void initialize_char() {
    g_char = new expr(mk_constant(get_char_name()));
}

static void finalize_char() {
    delete g_char;
}

expr mk_unit(level const & l, bool prop) { return prop ? mk_true() : mk_unit(l); }
expr mk_unit_mk(level const & l, bool prop) { return prop ? mk_true_intro() : mk_unit_mk(l); }

expr mk_pprod(abstract_type_context & ctx, expr const & a, expr const & b, bool prop) {
    return prop ? mk_and(a, b) : mk_pprod(ctx, a, b);
}
expr mk_pprod_mk(abstract_type_context & ctx, expr const & a, expr const & b, bool prop) {
    return prop ? mk_and_intro(ctx, a, b) : mk_pprod_mk(ctx, a, b);
}
expr mk_pprod_fst(abstract_type_context & ctx, expr const & p, bool prop) {
    return prop ? mk_and_elim_left(ctx, p) : mk_pprod_fst(ctx, p);
}
expr mk_pprod_snd(abstract_type_context & ctx, expr const & p, bool prop) {
    return prop ? mk_and_elim_right(ctx, p) : mk_pprod_snd(ctx, p);
}

bool is_ite(expr const & e) {
    return is_app_of(e, get_ite_name(), 5);
}

bool is_ite(expr const & e, expr & c, expr & H, expr & A, expr & t, expr & f) {
    if (is_ite(e)) {
        buffer<expr> args;
        get_app_args(e, args);
        lean_assert(args.size() == 5);
        c = args[0]; H = args[1]; A = args[2]; t = args[3]; f = args[4];
        return true;
    } else {
        return false;
    }
}

bool is_iff(expr const & e) {
    return is_app_of(e, get_iff_name(), 2);
}

bool is_iff(expr const & e, expr & lhs, expr & rhs) {
    if (!is_iff(e))
        return false;
    lhs = app_arg(app_fn(e));
    rhs = app_arg(e);
    return true;
}
expr mk_iff(expr const & lhs, expr const & rhs) {
    return mk_app(mk_constant(get_iff_name()), lhs, rhs);
}
expr mk_iff_refl(expr const & a) {
    return mk_app(mk_constant(get_iff_refl_name()), a);
}
expr mk_propext(expr const & lhs, expr const & rhs, expr const & iff_pr) {
    return mk_app(mk_constant(get_propext_name()), lhs, rhs, iff_pr);
}

expr mk_eq(abstract_type_context & ctx, expr const & lhs, expr const & rhs) {
    expr A    = ctx.whnf(ctx.infer(lhs));
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_eq_name(), {lvl}), A, lhs, rhs);
}

expr mk_eq_refl(abstract_type_context & ctx, expr const & a) {
    expr A    = ctx.whnf(ctx.infer(a));
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_eq_refl_name(), {lvl}), A, a);
}

expr mk_eq_symm(abstract_type_context & ctx, expr const & H) {
    if (is_app_of(H, get_eq_refl_name()))
        return H;
    expr p    = ctx.whnf(ctx.infer(H));
    lean_assert(is_eq(p));
    expr lhs  = app_arg(app_fn(p));
    expr rhs  = app_arg(p);
    expr A    = ctx.infer(lhs);
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_eq_symm_name(), {lvl}), A, lhs, rhs, H);
}

expr mk_eq_trans(abstract_type_context & ctx, expr const & H1, expr const & H2) {
    if (is_app_of(H1, get_eq_refl_name()))
        return H2;
    if (is_app_of(H2, get_eq_refl_name()))
        return H1;
    expr p1    = ctx.whnf(ctx.infer(H1));
    expr p2    = ctx.whnf(ctx.infer(H2));
    lean_assert(is_eq(p1) && is_eq(p2));
    expr lhs1  = app_arg(app_fn(p1));
    expr rhs1  = app_arg(p1);
    expr rhs2  = app_arg(p2);
    expr A     = ctx.infer(lhs1);
    level lvl  = get_level(ctx, A);
    return mk_app({mk_constant(get_eq_trans_name(), {lvl}), A, lhs1, rhs1, rhs2, H1, H2});
}

expr mk_eq_subst(abstract_type_context & ctx, expr const & motive,
                 expr const & x, expr const & y, expr const & xeqy, expr const & h) {
    expr A    = ctx.infer(x);
    level l1  = get_level(ctx, A);
    expr r    = mk_constant(get_eq_subst_name(), {l1});
    return mk_app({r, A, x, y, motive, xeqy, h});
}

expr mk_eq_subst(abstract_type_context & ctx, expr const & motive, expr const & xeqy, expr const & h) {
    expr xeqy_type = ctx.whnf(ctx.infer(xeqy));
    return mk_eq_subst(ctx, motive, app_arg(app_fn(xeqy_type)), app_arg(xeqy_type), xeqy, h);
}

expr mk_congr_arg(abstract_type_context & ctx, expr const & f, expr const & H) {
    expr eq = ctx.relaxed_whnf(ctx.infer(H));
    expr pi = ctx.relaxed_whnf(ctx.infer(f));
    expr A, B, lhs, rhs;
    lean_verify(is_eq(eq, A, lhs, rhs));
    lean_assert(is_arrow(pi));
    B = binding_body(pi);
    level lvl_1  = get_level(ctx, A);
    level lvl_2  = get_level(ctx, B);
    return ::lean::mk_app({mk_constant(get_congr_arg_name(), {lvl_1, lvl_2}), A, B, lhs, rhs, f, H});
}

expr mk_subsingleton_elim(abstract_type_context & ctx, expr const & h, expr const & x, expr const & y) {
    expr A  = ctx.infer(x);
    level l = get_level(ctx, A);
    expr r  = mk_constant(get_subsingleton_elim_name(), {l});
    return mk_app({r, A, h, x, y});
}

expr mk_heq(abstract_type_context & ctx, expr const & lhs, expr const & rhs) {
    expr A    = ctx.whnf(ctx.infer(lhs));
    expr B    = ctx.whnf(ctx.infer(rhs));
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_heq_name(), {lvl}), A, lhs, B, rhs);
}

bool is_eq_rec_core(expr const & e) {
    expr const & fn = get_app_fn(e);
    return is_constant(fn) && const_name(fn) == get_eq_rec_name();
}

bool is_eq_rec(expr const & e) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        return false;
    return const_name(fn) == get_eq_rec_name();
}

bool is_eq_drec(expr const & e) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn))
        return false;
    return const_name(fn) == get_eq_drec_name();
}

bool is_eq(expr const & e) {
    return is_app_of(e, get_eq_name(), 3);
}

bool is_eq(expr const & e, expr & lhs, expr & rhs) {
    if (!is_eq(e))
        return false;
    lhs = app_arg(app_fn(e));
    rhs = app_arg(e);
    return true;
}

bool is_eq(expr const & e, expr & A, expr & lhs, expr & rhs) {
    if (!is_eq(e))
        return false;
    A   = app_arg(app_fn(app_fn(e)));
    lhs = app_arg(app_fn(e));
    rhs = app_arg(e);
    return true;
}

bool is_eq_a_a(expr const & e) {
    if (!is_eq(e))
        return false;
    expr lhs = app_arg(app_fn(e));
    expr rhs = app_arg(e);
    return lhs == rhs;
}

bool is_eq_a_a(abstract_type_context & ctx, expr const & e) {
    if (!is_eq(e))
        return false;
    expr lhs = app_arg(app_fn(e));
    expr rhs = app_arg(e);
    return ctx.is_def_eq(lhs, rhs);
}

bool is_heq(expr const & e) {
    return is_app_of(e, get_heq_name(), 4);
}

bool is_heq(expr const & e, expr & A, expr & lhs, expr & B, expr & rhs) {
    if (is_heq(e)) {
        buffer<expr> args;
        get_app_args(e, args);
        lean_assert(args.size() == 4);
        A = args[0]; lhs = args[1]; B = args[2]; rhs = args[3];
        return true;
    } else {
        return false;
    }
}

bool is_heq(expr const & e, expr & lhs, expr & rhs) {
    expr A, B;
    return is_heq(e, A, lhs, B, rhs);
}

expr mk_cast(abstract_type_context & ctx, expr const & H, expr const & e) {
    expr type = ctx.relaxed_whnf(ctx.infer(H));
    expr A, B;
    if (!is_eq(type, A, B))
        throw exception("cast failed, equality proof expected");
    level lvl = get_level(ctx, A);
    return mk_app(mk_constant(get_cast_name(), {lvl}), A, B, H, e);
}

expr mk_false() {
    return mk_constant(get_false_name());
}

expr mk_empty() {
    return mk_constant(get_empty_name());
}

bool is_false(expr const & e) {
    return is_constant(e) && const_name(e) == get_false_name();
}

bool is_empty(expr const & e) {
    return is_constant(e) && const_name(e) == get_empty_name();
}

expr mk_false_rec(abstract_type_context & ctx, expr const & f, expr const & t) {
    level t_lvl = get_level(ctx, t);
    return mk_app(mk_constant(get_false_rec_name(), {t_lvl}), t, f);
}

bool is_or(expr const & e) {
    return is_app_of(e, get_or_name(), 2);
}

bool is_or(expr const & e, expr & A, expr & B) {
    if (is_or(e)) {
        A = app_arg(app_fn(e));
        B = app_arg(e);
        return true;
    } else {
        return false;
    }
}

bool is_not(expr const & e, expr & a) {
    if (is_app_of(e, get_not_name(), 1)) {
        a = app_arg(e);
        return true;
    } else if (is_pi(e) && is_false(binding_body(e))) {
        a = binding_domain(e);
        return true;
    } else {
        return false;
    }
}

bool is_not_or_ne(expr const & e, expr & a) {
    if (is_not(e, a)) {
        return true;
    } else if (is_app_of(e, get_ne_name(), 3)) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        expr new_fn     = mk_constant(get_eq_name(), const_levels(fn));
        a               = mk_app(new_fn, args);
        return true;
    } else {
        return false;
    }
}

expr mk_not(expr const & e) {
    return mk_app(mk_constant(get_not_name()), e);
}

expr mk_absurd(abstract_type_context & ctx, expr const & t, expr const & e, expr const & not_e) {
    level t_lvl  = get_level(ctx, t);
    expr  e_type = ctx.infer(e);
    return mk_app(mk_constant(get_absurd_name(), {t_lvl}), e_type, t, e, not_e);
}

bool is_type(expr const & e) {
    buffer<expr> telescope;
    return is_sort(to_telescope(true, e, telescope, optional<binder_info>()));
}

bool is_exists(expr const & e, expr & A, expr & p) {
    if (is_app_of(e, get_Exists_name(), 2)) {
        A = app_arg(app_fn(e));
        p = app_arg(e);
        return true;
    } else {
        return false;
    }
}

bool is_exists(expr const & e) {
    return is_app_of(e, get_Exists_name(), 2);
}

optional<expr> get_binary_op(expr const & e) {
    if (!is_app(e) || !is_app(app_fn(e)))
        return none_expr();
    return some_expr(app_fn(app_fn(e)));
}

optional<expr> get_binary_op(expr const & e, expr & arg1, expr & arg2) {
    if (auto op = get_binary_op(e)) {
        arg1 = app_arg(app_fn(e));
        arg2 = app_arg(e);
        return some_expr(*op);
    } else {
        return none_expr();
    }
}

expr mk_nary_app(expr const & op, buffer<expr> const & nary_args) {
    return mk_nary_app(op, nary_args.size(), nary_args.data());
}

expr mk_nary_app(expr const & op, unsigned num_nary_args, expr const * nary_args) {
    lean_assert(num_nary_args >= 2);
    // f x1 x2 x3 ==> f x1 (f x2 x3)
    expr e = mk_app(op, nary_args[num_nary_args - 2], nary_args[num_nary_args - 1]);
    for (int i = num_nary_args - 3; i >= 0; --i) {
        e = mk_app(op, nary_args[i], e);
    }
    return e;
}

bool is_annotated_lamba(expr const & e) {
    return
        is_lambda(e) ||
        (is_annotation(e) && is_lambda(get_nested_annotation_arg(e)));
}

bool is_annotated_head_beta(expr const & t) {
    return is_app(t) && is_annotated_lamba(get_app_fn(t));
}

expr annotated_head_beta_reduce(expr const & t) {
    if (!is_annotated_head_beta(t)) {
        return t;
    } else {
        buffer<expr> args;
        expr f = get_app_rev_args(t, args);
        if (is_annotation(f))
            f = get_nested_annotation_arg(f);
        lean_assert(is_lambda(f));
        return annotated_head_beta_reduce(apply_beta(f, args.size(), args.data()));
    }
}

expr try_eta(expr const & e) {
    if (is_lambda(e)) {
        expr const & b = binding_body(e);
        if (is_lambda(b)) {
            expr new_b = try_eta(b);
            if (is_eqp(b, new_b)) {
                return e;
            } else if (is_app(new_b) && is_var(app_arg(new_b), 0) && !has_free_var(app_fn(new_b), 0)) {
                return lower_free_vars(app_fn(new_b), 1);
            } else {
                return update_binding(e, binding_domain(e), new_b);
            }
        } else if (is_app(b) && is_var(app_arg(b), 0) && !has_free_var(app_fn(b), 0)) {
            return lower_free_vars(app_fn(b), 1);
        } else {
            return e;
        }
    } else {
        return e;
    }
}

template<bool Eta, bool Beta>
class eta_beta_reduce_fn : public replace_visitor {
public:
    virtual expr visit_app(expr const & e) override {
        expr e1 = replace_visitor::visit_app(e);
        if (Beta && is_head_beta(e1)) {
            return visit(head_beta_reduce(e1));
        } else {
            return e1;
        }
    }

    virtual expr visit_lambda(expr const & e) override {
        expr e1 = replace_visitor::visit_lambda(e);
        if (Eta) {
            while (true) {
                expr e2 = try_eta(e1);
                if (is_eqp(e1, e2))
                    return e1;
                else
                    e1 = e2;
            }
        } else {
            return e1;
        }
    }
};

expr beta_reduce(expr t) {
    return eta_beta_reduce_fn<false, true>()(t);
}

expr eta_reduce(expr t) {
    return eta_beta_reduce_fn<true, false>()(t);
}

expr beta_eta_reduce(expr t) {
    return eta_beta_reduce_fn<true, true>()(t);
}

expr infer_implicit_params(expr const & type, unsigned nparams, implicit_infer_kind k) {
    switch (k) {
    case implicit_infer_kind::Implicit: {
        bool strict = true;
        return infer_implicit(type, nparams, strict);
    }
    case implicit_infer_kind::RelaxedImplicit: {
        bool strict = false;
        return infer_implicit(type, nparams, strict);
    }
    case implicit_infer_kind::None:
        return type;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool get_constructor_rec_args(environment const & env, expr const & e, buffer<pair<expr, unsigned>> & rec_args) {
    type_checker ctx(env);
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    if (!is_constant(fn)) return false;
    optional<name> I_name = inductive::is_intro_rule(env, const_name(fn));
    if (!I_name) return false;
    expr type       = env.get(const_name(fn)).get_type();
    buffer<expr> tele;
    to_telescope(ctx, type, tele);
    if (tele.size() != args.size()) return false;
    for (unsigned i = 0; i < tele.size(); i++) {
        expr d = tele[i];
        buffer<expr> tele_tele;
        expr r  = to_telescope(ctx, mlocal_type(d), tele_tele);
        expr fn = get_app_fn(r);
        if (is_constant(fn, *I_name)) {
            rec_args.push_back(mk_pair(args[i], tele_tele.size()));
        }
    }
    return true;
}

static expr * g_bool = nullptr;
static expr * g_bool_tt = nullptr;
static expr * g_bool_ff = nullptr;

void initialize_bool() {
    g_bool = new expr(mk_constant(get_bool_name()));
    g_bool_ff = new expr(mk_constant(get_bool_ff_name()));
    g_bool_tt = new expr(mk_constant(get_bool_tt_name()));
}

void finalize_bool() {
    delete g_bool;
    delete g_bool_ff;
    delete g_bool_tt;
}

expr mk_bool() { return *g_bool; }
expr mk_bool_tt() { return *g_bool_tt; }
expr mk_bool_ff() { return *g_bool_ff; }
expr to_bool_expr(bool b) { return b ? mk_bool_tt() : mk_bool_ff(); }

name get_dep_recursor(environment const & env, name const & n) {
    if (is_inductive_predicate(env, n))
        return name(n, "drec");
    else
        return name(n, "rec");
}

name get_dep_cases_on(environment const & env, name const & n) {
    if (is_inductive_predicate(env, n))
        return name(n, "dcases_on");
    else
        return name(n, "cases_on");
}

static char const * g_aux_meta_rec_prefix = "_meta_aux";

name mk_aux_meta_rec_name(name const & n) {
    return name(n, g_aux_meta_rec_prefix);
}

optional<name> is_aux_meta_rec_name(name const & n) {
    if (!n.is_atomic() && n.is_string() && strcmp(n.get_string(), g_aux_meta_rec_prefix) == 0) {
        return optional<name>(n.get_prefix());
    } else {
        return optional<name>();
    }
}

optional<name> name_lit_to_name(expr const & name_lit) {
    if (is_constant(name_lit, get_name_anonymous_name()))
        return optional<name>(name());
    if (is_app_of(name_lit, get_name_mk_string_name(), 2)) {
        if (auto str = to_string(app_arg(app_fn(name_lit))))
        if (auto p   = name_lit_to_name(app_arg(name_lit)))
            return optional<name>(name(*p, str->c_str()));
    }
    return optional<name>();
}

static expr * g_tactic_unit = nullptr;

expr mk_tactic_unit() {
    return *g_tactic_unit;
}

static std::string * g_version_string = nullptr;
std::string const & get_version_string() { return *g_version_string; }

void initialize_library_util() {
    g_true           = new expr(mk_constant(get_true_name()));
    g_true_intro     = new expr(mk_constant(get_true_intro_name()));
    g_and            = new expr(mk_constant(get_and_name()));
    g_and_intro      = new expr(mk_constant(get_and_intro_name()));
    g_and_elim_left  = new expr(mk_constant(get_and_elim_left_name()));
    g_and_elim_right = new expr(mk_constant(get_and_elim_right_name()));
    g_tactic_unit    = new expr(mk_app(mk_constant(get_tactic_name(), {mk_level_zero()}), mk_constant(get_unit_name())));
    initialize_nat();
    initialize_int();
    initialize_char();
    initialize_bool();

    sstream out;

    out << LEAN_VERSION_MAJOR << "."
        << LEAN_VERSION_MINOR << "." << LEAN_VERSION_PATCH;
    if (std::strlen(LEAN_SPECIAL_VERSION_DESC) > 0) {
        out << ", " << LEAN_SPECIAL_VERSION_DESC;
    }
    if (std::strcmp(LEAN_GITHASH, "GITDIR-NOTFOUND") == 0) {
        if (std::strcmp(LEAN_PACKAGE_VERSION, "NOT-FOUND") != 0) {
            out << ", package " << LEAN_PACKAGE_VERSION;
        }
    } else {
        out << ", commit " << std::string(LEAN_GITHASH).substr(0, 12);
    }
    g_version_string = new std::string(out.str());
}

void finalize_library_util() {
    delete g_version_string;
    finalize_bool();
    finalize_int();
    finalize_nat();
    finalize_char();
    delete g_true;
    delete g_true_intro;
    delete g_and;
    delete g_and_intro;
    delete g_and_elim_left;
    delete g_and_elim_right;
    delete g_tactic_unit;
}
}
