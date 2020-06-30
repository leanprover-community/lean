/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <algorithm>
#include <limits>
#include <string>
#include <util/utf8.h>
#include "library/sorry.h"
#include "util/flet.h"
#include "util/fresh_name.h"
#include "util/sstream.h"
#include "kernel/replace_fn.h"
#include "kernel/free_vars.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/annotation.h"
#include "library/aliases.h"
#include "library/class.h"
#include "library/scoped_ext.h"
#include "library/expr_pair.h"
#include "library/placeholder.h"
#include "library/private.h"
#include "library/protected.h"
#include "library/quote.h"
#include "library/explicit.h"
#include "library/typed_expr.h"
#include "library/num.h"
#include "library/util.h"
#include "library/print.h"
#include "library/pp_options.h"
#include "library/delayed_abstraction.h"
#include "library/constants.h"
#include "library/replace_visitor.h"
#include "library/string.h"
#include "library/type_context.h"
#include "library/idx_metavar.h"
#include "library/equations_compiler/equations.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/smt/hinst_lemmas.h"
#include "library/compiler/comp_irrelevant.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/rec_fn_macro.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/util.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/tokens.h"
#include "library/vm/vm_eformat.h"
#include "library/trace.h"

namespace lean {
static format * g_ellipsis_n_fmt  = nullptr;
static format * g_ellipsis_fmt    = nullptr;
static format * g_placeholder_fmt = nullptr;
static format * g_lambda_n_fmt    = nullptr;
static format * g_lambda_fmt      = nullptr;
static format * g_forall_n_fmt    = nullptr;
static format * g_forall_fmt      = nullptr;
static format * g_pi_n_fmt        = nullptr;
static format * g_pi_fmt          = nullptr;
static format * g_arrow_n_fmt     = nullptr;
static format * g_arrow_fmt       = nullptr;
static format * g_let_fmt         = nullptr;
static format * g_in_fmt          = nullptr;
static format * g_assign_fmt      = nullptr;
static format * g_have_fmt        = nullptr;
static format * g_from_fmt        = nullptr;
static format * g_visible_fmt     = nullptr;
static format * g_show_fmt        = nullptr;
static format * g_explicit_fmt    = nullptr;
static format * g_partial_explicit_fmt    = nullptr;

class nat_numeral_pp {
    name m_nat;
    expr m_nat_zero;
    expr m_nat_succ;
public:
    nat_numeral_pp():
        m_nat(get_nat_name()),
        m_nat_zero(mk_constant(get_nat_zero_name())),
        m_nat_succ(mk_constant(get_nat_succ_name())) {
    }

    // Return an unsigned if \c e if of the form (succ^k zero), and k
    // fits in a machine unsigned integer.
    optional<unsigned> to_unsigned(expr const & e) const {
        unsigned r = 0;
        expr const * it = &e;
        while (true) {
            if (*it == m_nat_zero) {
                return optional<unsigned>(r);
            } else if (is_app(*it) && app_fn(*it) == m_nat_succ) {
                if (r == std::numeric_limits<unsigned>::max())
                    return optional<unsigned>(); // just in case, it does not really happen in practice
                r++;
                it = &app_arg(*it);
            } else if (is_zero(get_app_fn(*it))) {
                return optional<unsigned>(r);
            } else {
                return optional<unsigned>();
            }
        }
    }
};

static nat_numeral_pp * g_nat_numeral_pp = nullptr;

static optional<unsigned> to_unsigned(expr const & e) {
    return g_nat_numeral_pp->to_unsigned(e);
}

static name * g_pp_using_anonymous_constructor = nullptr;
static name * g_pp_nodot = nullptr;

bool pp_using_anonymous_constructor(environment const & env, name const & n) {
    return has_attribute(env, *g_pp_using_anonymous_constructor, n);
}

bool pp_nodot(environment const & env, name const & n) {
    return has_attribute(env, *g_pp_nodot, n);
}

void initialize_pp() {
    g_ellipsis_n_fmt  = new format(highlight(format("…")));
    g_ellipsis_fmt    = new format(highlight(format("...")));
    g_placeholder_fmt = new format(highlight(format("_")));
    g_lambda_n_fmt    = new format(highlight_keyword(format("λ")));
    g_lambda_fmt      = new format(highlight_keyword(format("fun")));
    g_forall_n_fmt    = new format(highlight_keyword(format("∀")));
    g_forall_fmt      = new format(highlight_keyword(format("forall")));
    g_pi_n_fmt        = new format(highlight_keyword(format("Π")));
    g_pi_fmt          = new format(highlight_keyword(format("Pi")));
    g_arrow_n_fmt     = new format(highlight_keyword(format("→")));
    g_arrow_fmt       = new format(highlight_keyword(format("->")));
    g_let_fmt         = new format(highlight_keyword(format("let")));
    g_in_fmt          = new format(highlight_keyword(format("in")));
    g_assign_fmt      = new format(highlight_keyword(format(":=")));
    g_have_fmt        = new format(highlight_keyword(format("have")));
    g_from_fmt        = new format(highlight_keyword(format("from")));
    g_visible_fmt     = new format(highlight_keyword(format("[visible]")));
    g_show_fmt        = new format(highlight_keyword(format("show")));
    g_explicit_fmt    = new format(highlight_keyword(format("@")));
    g_partial_explicit_fmt    = new format(highlight_keyword(format("@@")));
    g_nat_numeral_pp  = new nat_numeral_pp();

    g_pp_using_anonymous_constructor = new name("pp_using_anonymous_constructor");
    g_pp_nodot = new name("pp_nodot");

    register_system_attribute(basic_attribute::with_check(
                                  *g_pp_using_anonymous_constructor,
                                  "if a structure S is marked with this attribute, then its constructor applications "
                                  "are pretty printed using the anonymous constructor",
                                  [](environment const & env, name const & d, bool) -> void {
                                      if (!is_structure(env, d))
                                          throw exception(
                                              "invalid 'pp_using_anonymous_constructor' use, "
                                              "only structures can be marked with this attribute");
                                              }));
    register_system_attribute(basic_attribute(*g_pp_nodot, "Do not pretty-print using dot-notation."));
}

void finalize_pp() {
    delete g_pp_nodot;
    delete g_pp_using_anonymous_constructor;
    delete g_nat_numeral_pp;
    delete g_ellipsis_n_fmt;
    delete g_ellipsis_fmt;
    delete g_placeholder_fmt;
    delete g_lambda_n_fmt;
    delete g_lambda_fmt;
    delete g_forall_n_fmt;
    delete g_forall_fmt;
    delete g_pi_n_fmt;
    delete g_pi_fmt;
    delete g_arrow_n_fmt;
    delete g_arrow_fmt;
    delete g_let_fmt;
    delete g_in_fmt;
    delete g_assign_fmt;
    delete g_have_fmt;
    delete g_from_fmt;
    delete g_visible_fmt;
    delete g_show_fmt;
    delete g_partial_explicit_fmt;
    delete g_explicit_fmt;
}

/** \brief We assume a metavariable name has a suggestion embedded in it WHEN its
    last component is a string. */
static bool has_embedded_suggestion(name const & m) {
    return m.is_string();
}

/** \see extract_suggestion */
static name extract_suggestion_core(name const & m) {
    if (m.is_string()) {
        if (m.is_atomic())
            return m;
        else
            return name(extract_suggestion_core(m.get_prefix()), m.get_string());
    } else {
        return name();
    }
}

/** \brief Extract "suggested name" embedded in a metavariable name

    \pre has_embedded_suggestion(m)
*/
static name extract_suggestion(name const & m) {
    lean_assert(has_embedded_suggestion(m));
    name r = extract_suggestion_core(m);
    lean_assert(!r.is_anonymous());
    return r;
}
template<class T>
name pretty_fn<T>::mk_metavar_name(name const & m, optional<name> const & prefix) {
    if (auto it = m_purify_meta_table.find(m))
        return *it;
    if (has_embedded_suggestion(m)) {
        name suggested = extract_suggestion(m);
        name r         = suggested;
        unsigned i     = 1;
        while (m_purify_used_metas.contains(r)) {
            r = suggested.append_after(i);
            i++;
        }
        m_purify_used_metas.insert(r);
        m_purify_meta_table.insert(m, r);
        return r;
    } else {
        name new_m;
        if (prefix)
            new_m = prefix->append_after(m_next_meta_idx);
        else
            new_m = m_meta_prefix.append_after(m_next_meta_idx);
        m_next_meta_idx++;
        m_purify_meta_table.insert(m, new_m);
        return new_m;
    }
}
template<class T>
name pretty_fn<T>::mk_local_name(name const & n, name const & suggested) {
    if (!m_purify_locals)
        return suggested;
    if (auto it = m_purify_local_table.find(n))
        return *it;
    unsigned i = 1;
    name r = suggested;
    while (m_purify_used_locals.contains(r)) {
        r = suggested.append_after(i);
        i++;
    }
    m_purify_used_locals.insert(r);
    m_purify_local_table.insert(n, r);
    return r;
}
template<class T>
level pretty_fn<T>::purify(level const & l) {
    if (!m_universes || !m_purify_metavars || !has_meta(l))
        return l;
    return replace(l, [&](level const & l) {
            if (!has_meta(l))
                return some_level(l);
            if (is_metavar_decl_ref(l))
                return some_level(mk_meta_univ(mk_metavar_name(meta_id(l), "l")));
            if (is_meta(l) && !is_idx_metauniv(l))
                return some_level(mk_meta_univ(mk_metavar_name(meta_id(l))));
            return none_level();
        });
}
template<class T>
expr pretty_fn<T>::infer_type(expr const & e) {
    try {
        return m_ctx.infer(e);
    } catch (exception &) {
        expr dummy = mk_Prop();
        return dummy;
    }
}

/** \brief Make sure that all metavariables have reasonable names,
    and for all local constants l1 l2, mlocal_pp_name(l1) != mlocal_pp_name(l2).

    \remark pretty_fn will create new local constants when pretty printing,
    but it will make sure that the new constants will not produce collisions.

    \remark We do not purify metavariable names IF the user provided them.
    We use the test (mlocal_name(e) == mlocal_pp_name(e)) to decide whether
    the user provided the name or not.
*/
template<class T>
expr pretty_fn<T>::purify(expr const & e) {
    if (!has_expr_metavar(e) && !has_local(e) && (!m_universes || !has_univ_metavar(e)))
        return e;
    return replace(e, [&](expr const & e, unsigned) {
            if (!has_expr_metavar(e) && !has_local(e) && (!m_universes || !has_univ_metavar(e))) {
                return some_expr(e);
            } else if (m_purify_metavars && is_metavar_decl_ref(e) && mlocal_name(e) == mlocal_pp_name(e)) {
                return some_expr(mk_metavar(mk_metavar_name(mlocal_name(e), "m"), infer_type(e)));
            } else if (m_purify_metavars && is_metavar(e) && mlocal_name(e) == mlocal_pp_name(e) && !is_idx_metavar(e)) {
                return some_expr(mk_metavar(mk_metavar_name(mlocal_name(e)), infer_type(e)));
            } else if (is_local(e)) {
                return some_expr(mk_local(mlocal_name(e), mk_local_name(mlocal_name(e), mlocal_pp_name(e)),
                                          infer_type(e), local_info(e)));
            } else if (is_constant(e)) {
                return some_expr(update_constant(e, map(const_levels(e), [&](level const & l) { return purify(l); })));
            } else if (is_sort(e)) {
                return some_expr(update_sort(e, purify(sort_level(e))));
            } else {
                return none_expr();
            }
        });
}
template<class T>
void pretty_fn<T>::set_options_core(options const & _o) {
    options o = _o;
    bool all          = get_pp_all(o);
    if (all) {
        o = o.update_if_undef(get_pp_implicit_name(), true);
        o = o.update_if_undef(get_pp_proofs_name(), true);
        o = o.update_if_undef(get_pp_coercions_name(), true);
        o = o.update_if_undef(get_pp_notation_name(), false);
        o = o.update_if_undef(get_pp_universes_name(), true);
        o = o.update_if_undef(get_pp_full_names_name(), true);
        o = o.update_if_undef(get_pp_beta_name(), false);
        o = o.update_if_undef(get_pp_numerals_name(), false);
        o = o.update_if_undef(get_pp_strings_name(), false);
        o = o.update_if_undef(get_pp_binder_types_name(), true);
        o = o.update_if_undef(get_pp_generalized_field_notation_name(), false);
    }
    m_options           = o;
    m_indent            = get_pp_indent(o);
    m_max_depth         = get_pp_max_depth(o);
    m_max_steps         = get_pp_max_steps(o);
    m_implict           = get_pp_implicit(o);
    m_proofs            = get_pp_proofs(o);
    m_unicode           = get_pp_unicode(o);
    m_coercion          = get_pp_coercions(o);
    m_notation          = get_pp_notation(o);
    m_universes         = get_pp_universes(o);
    m_full_names        = get_pp_full_names(o);
    m_private_names     = get_pp_private_names(o);
    m_purify_metavars   = get_pp_purify_metavars(o);
    m_purify_locals     = get_pp_purify_locals(o);
    m_locals_full_names = get_pp_locals_full_names(o);
    m_beta              = get_pp_beta(o);
    m_numerals          = get_pp_numerals(o);
    m_strings           = get_pp_strings(o);
    m_preterm           = get_pp_preterm(o);
    m_binder_types      = get_pp_binder_types(o);
    m_hide_comp_irrel   = get_pp_hide_comp_irrel(o);
    m_delayed_abstraction  = get_pp_delayed_abstraction(o);
    m_use_holes         = get_pp_use_holes(o);
    m_annotations       = get_pp_annotations(o);
    m_hide_full_terms   = get_formatter_hide_full_terms(o);
    m_num_nat_coe       = m_numerals;
    m_structure_instances = get_pp_structure_instances(o);
    m_structure_instances_qualifier = get_pp_structure_instances_qualifier(o);
    m_structure_projections         = get_pp_structure_projections(o);
    m_generalized_field_notation = get_pp_generalized_field_notation(o);
    m_links             = get_pp_links(o);
}
template<class T>
void pretty_fn<T>::set_options(options const & o) {
    if (is_eqp(o, m_options))
        return;
    set_options_core(o);
}
template<class T>
format pretty_fn<T>::pp_child(level const & l) {
    if (is_explicit(l) || is_param(l) || is_meta(l)) {
        return pp_level(l);
    } else {
        return paren(pp_level(l));
    }
}
template<class T>
format pretty_fn<T>::pp_max(level l) {
    lean_assert(is_max(l) || is_imax(l));
    format r  = format(is_max(l) ? "max" : "imax");
    level lhs = is_max(l) ? max_lhs(l) : imax_lhs(l);
    level rhs = is_max(l) ? max_rhs(l) : imax_rhs(l);
    r += nest(m_indent, compose(line(), pp_child(lhs)));
    while (kind(rhs) == kind(l)) {
        l = rhs;
        lhs = is_max(l) ? max_lhs(l) : imax_lhs(l);
        rhs = is_max(l) ? max_rhs(l) : imax_rhs(l);
        r += nest(m_indent, compose(line(), pp_child(lhs)));
    }
    r += nest(m_indent, compose(line(), pp_child(rhs)));
    return group(r);
}
template<class T>
format pretty_fn<T>::pp_meta(level const & l) {
    if (m_universes) {
        if (is_idx_metauniv(l)) {
            return format((sstream() << "?u_" << to_meta_idx(l)).str());
        } else if (is_metavar_decl_ref(l)) {
            return format((sstream() << "?l_" << get_metavar_decl_ref_suffix(l)).str());
        } else {
            return compose(format("?"), format(meta_id(l)));
        }
    } else {
        return format("?");
    }
}
template<class T>
format pretty_fn<T>::pp_level(level const & l) {
    if (is_explicit(l)) {
        lean_assert(get_depth(l) > 0);
        return format(get_depth(l) - 1);
    } else {
        switch (kind(l)) {
        case level_kind::Zero:
            lean_unreachable(); // LCOV_EXCL_LINE
        case level_kind::Param:
            return format(param_id(l));
        case level_kind::Meta:
            return pp_meta(l);
        case level_kind::Succ: {
            auto p = to_offset(l);
            return pp_child(p.first) + format("+") + format(p.second);
        }
        case level_kind::Max: case level_kind::IMax:
            return pp_max(l);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
}
template<class T>
bool pretty_fn<T>::is_implicit(expr const & f) {
    // Remark: we assume preterms do not have implicit arguments,
    // since they have not been elaborated yet.
    // Moreover, the type checker will probably produce an error
    // when trying to infer type information
    if (m_implict || m_preterm)
        return false; // showing implicit arguments
    if (!closed(f)) {
        // the Lean type checker assumes expressions are closed.
        return false;
    }
    try {
        expr t = m_ctx.relaxed_whnf(m_ctx.infer(f));
        if (is_pi(t)) {
            binder_info bi = binding_info(t);
            return bi.is_implicit() || bi.is_strict_implicit() || bi.is_inst_implicit();
        } else {
            return false;
        }
    } catch (exception &) {
        return false;
    }
}
template<class T>
bool pretty_fn<T>::is_default_arg_app(expr const & e) {
    if (m_implict || m_preterm)
        return false; // showing default arguments
    if (!closed(app_fn(e))) {
        // the Lean type checker assumes expressions are closed.
        return false;
    }
    try {
        expr t = m_ctx.relaxed_whnf(m_ctx.infer(app_fn(e)));
        if (is_pi(t)) {
            expr arg_type = binding_domain(t);
            t = binding_body(t);
            if (!is_pi(t) && !is_var(t) && is_app_of(arg_type, get_opt_param_name(), 2)) {
                expr defval = app_arg(arg_type);
                return closed(defval) && defval == app_arg(e);
            }
        }
    } catch (exception &) { }
    return false;
}
template<class T>
bool pretty_fn<T>::is_prop(expr const & e) {
    try {
        expr t = m_ctx.relaxed_whnf(m_ctx.infer(e));
        return t == mk_Prop();
    } catch (exception &) {
        return false;
    }
}
template<class T>
auto pretty_fn<T>::add_paren_if_needed(result const & r, unsigned bp) -> result {
    if (r.rbp() < bp) {
        return result(paren(r.fmt()));
    } else {
        return r;
    }
}

static expr consume_ref_annotations(expr const & e) {
    if (is_explicit(e))
        return consume_ref_annotations(get_explicit_arg(e));
    else
        return e;
}

enum local_ref_kind { LocalRef, OverridenLocalRef, NotLocalRef };

static local_ref_kind check_local_ref(environment const & env, expr const & e, unsigned & num_ref_univ_params) {
    expr const & rfn = get_app_fn(e);
    if (!is_constant(rfn))
        return NotLocalRef;
    auto ref = get_local_ref(env, const_name(rfn));
    if (!ref)
        return NotLocalRef;
    if (is_as_atomic(*ref))
        ref = get_as_atomic_arg(*ref);
    buffer<expr> ref_args, e_args;
    expr ref_fn = consume_ref_annotations(get_app_args(*ref, ref_args));
    get_app_args(e, e_args);
    if (!is_constant(ref_fn) || e_args.size() != ref_args.size()) {
        return NotLocalRef;
    }
    for (unsigned i = 0; i < e_args.size(); i++) {
        expr e_arg   = e_args[i];
        expr ref_arg = consume_ref_annotations(ref_args[i]);
        if (!is_local(e_arg) || !is_local(ref_arg) || mlocal_pp_name(e_arg) != mlocal_pp_name(ref_arg))
            return OverridenLocalRef;
    }
    num_ref_univ_params = length(const_levels(ref_fn));
    buffer<level> lvls;
    to_buffer(const_levels(rfn), lvls);
    if (lvls.size() < num_ref_univ_params) {
        return NotLocalRef;
    }
    for (unsigned i = 0; i < num_ref_univ_params; i++) {
        level const & l = lvls[i];
        if (!is_param(l)) {
            return OverridenLocalRef;
        }
        for (unsigned j = 0; j < i; j++)
            if (lvls[i] == lvls[j]) {
                return OverridenLocalRef;
            }
    }
    return LocalRef;
}

static bool is_local_ref(environment const & env, expr const & e) {
    unsigned num_ref_univ_params;
    return check_local_ref(env, e, num_ref_univ_params) == LocalRef;
}
template<class T>
auto pretty_fn<T>::pp_overriden_local_ref(expr const & e) -> result {
    buffer<expr> args;
    expr const & fn = get_app_args(e, args);
    result res_fn;
    {
        flet<bool> set1(m_full_names, true);
        address_scope scope(*this, expr_address::fn(args.size()));
        res_fn = pp_const(fn, some(0u));
    }
    T fn_fmt    = res_fn.fmt();
    if (const_name(fn).is_atomic()){
        fn_fmt = T("_root_.") + fn_fmt;
    }
    if (m_implict && has_implicit_args(fn)) {
        fn_fmt = *g_explicit_fmt + fn_fmt;
    }
    T r_fmt = mk_link(const_name(fn), fn_fmt);
    expr curr_fn = fn;
    for (unsigned i = 0; i < args.size(); i++) {
        expr const & arg = args[i];
        if (m_implict || !is_implicit(curr_fn)) {
            result res_arg   = pp_child_at(arg, max_bp(), expr_address::app(args.size(), i));
            r_fmt = group(compose(r_fmt, nest(m_indent, compose(line(), res_arg.fmt()))));
        }
        curr_fn = mk_app(curr_fn, arg);
    }
    return result(max_bp()-1, r_fmt);
}

// Return some result if \c e is of the form (c p_1 ... p_n) where
// c is a constant, and p_i's are parameters fixed in a section.
template<class T>
auto pretty_fn<T>::pp_local_ref(expr const & e) -> optional<result> {
    unsigned num_ref_univ_params;
    switch (check_local_ref(m_env, e, num_ref_univ_params)) {
    case NotLocalRef:
        return optional<result>();
    case LocalRef:
        return some(pp_const(get_app_fn(e), optional<unsigned>(num_ref_univ_params)));
    case OverridenLocalRef:
        return some(pp_overriden_local_ref(e));
    }
    lean_unreachable();
}

static bool is_coercion(expr const & e) {
    return is_app_of(e, get_coe_name()) && get_app_num_args(e) >= 4;
}

static bool is_coercion_fn(expr const & e) {
    return is_app_of(e, get_coe_fn_name()) && get_app_num_args(e) >= 3;
}

template<class T>
auto pretty_fn<T>::pp_hide_coercion(expr const & e, unsigned bp, bool ignore_hide) -> result {
    lean_assert(is_coercion(e));
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() == 4) { // e = @has_coe.coe _ _ _ x
        return pp_child_at(args[3], bp, expr_address::app(args.size(), 3), ignore_hide);
    } else {
        // e = (@has_coe.coe _ _ _ f) x y z
        expr new_e = mk_app(args.size() - 3, args.data() + 3);
        // new_e = f x y z
        // [todo] pp_child needs to know that `f` now has a different address.
        // Currently this will calculate the wrong address and cause bugs so we should give up for now.
        address_give_up_scope _(*this);
        return pp_child(new_e, bp, ignore_hide);
    }
}
template<class T>
auto pretty_fn<T>::pp_hide_coercion_fn(expr const & e, unsigned bp, bool ignore_hide) -> result {
    lean_assert(is_coercion_fn(e));
    buffer<expr> args;
    get_app_args(e, args);
    if (args.size() == 3) {
        return pp_child_at(args[2], bp, expr_address::app(args.size(), 2), ignore_hide);
    } else {
        expr new_e = mk_app(args.size() - 2, args.data() + 2);
        // [todo] pp_child needs to know that `f` now has a different address. (see above)
        address_give_up_scope _(*this);
        return pp_child(new_e, bp, ignore_hide);
    }
}
template<class T>
auto pretty_fn<T>::pp_child(expr const & e, unsigned bp, bool ignore_hide, bool below_implicit) -> result {
    if (is_app(e)) {
        if (auto r = pp_local_ref(e)){
            address_reset_scope ars(*this);
            return tag(ars.m_adr, e, add_paren_if_needed(*r, bp));
        }
        if (m_numerals) {
            if (auto n = to_num(e)) {
                return tag(m_address, e, pp_num(*n, bp));
            }
        }
        if (m_strings) {
            if (auto r = to_string(e)) {
                return tag(m_address, e, T(pp_string_literal(*r)));
            }
            if (auto r = to_char(m_ctx, e)) {
                return tag(m_address, e, T(pp_char_literal(*r)));
            }
        }
        expr const & f = app_fn(e);
        if (is_implicit(f)) {
            if (below_implicit) {
                return pp_child_at(f, bp, expr_address::fn(), ignore_hide, true);
            } else {
              address_scope _(*this, expr_address::fn());
              address_reset_scope ars(*this); 
              return tag(ars.m_adr, f, pp_child_at(f, bp, expr_address::fn(), ignore_hide, true));
            }
        } else if (!m_coercion && is_coercion(e)) {
            return pp_hide_coercion(e, bp, ignore_hide);
        } else if (!m_coercion && is_coercion_fn(e)) {
            return pp_hide_coercion_fn(e, bp, ignore_hide);
        }
    }
    if (below_implicit) {
        return add_paren_if_needed(pp_core(e, ignore_hide), bp);
    } else {
        return add_paren_if_needed(pp(e, ignore_hide), bp);
    }
}
template<class T>
auto pretty_fn<T>::pp_var(expr const & e) -> result {
    unsigned vidx = var_idx(e);
    return result(T("#") + T(vidx));
}
template<class T>
auto pretty_fn<T>::pp_sort(expr const & e) -> result {
    level u = sort_level(e);
    if (u == mk_level_zero()) {
        return result(T("Prop"));
    } else if (u == mk_level_one()) {
        return result(T("Type"));
    } else if (optional<level> u1 = dec_level(u)) {
        return result(max_bp()-1, group(T("Type") + space() + nest(5, pp_child(*u1))));
    } else {
        return result(max_bp()-1, group(T("Sort") + space() + nest(5, pp_child(u))));
    }
}
template<class T>
optional<name> pretty_fn<T>::is_aliased(name const & n) const {
    if (auto it = is_expr_aliased(m_env, n)) {
        // must check if we are not shadow by current namespace
        for (name const & ns : get_namespaces(m_env)) {
            if (!ns.is_anonymous() && m_env.find(ns + *it))
                return optional<name>();
        }
        return it;
    } else {
        return optional<name>();
    }
}
template<class T>
T pretty_fn<T>::escape(name const & n) {
    // also escape keyword-like names
    if (n.is_atomic() && n.is_string() && find(m_token_table, n.get_string())) {
        sstream ss;
        ss << "«" << n.get_string() << "»";
        return T(ss.str());
    }
    return T(n.escape());
}
template<class T>
T pretty_fn<T>::mk_link(name const & dest, T const & body) {
    if (m_links) {
        return T((sstream() << "\xee\x80\x80" << dest << "\xee\x80\x81").str()) +
            body + T("\xee\x80\x82");
    } else {
        return body;
    }
}
template<class T>
auto pretty_fn<T>::mk_link(name const & dest, result const & body) -> result {
    if (!m_links) return body;
    return result(body.lbp(), body.rbp(), mk_link(dest, body.fmt()));
}
template<class T>
T pretty_fn<T>::mk_link(expr const & dest, T const & body) {
    if (!m_links) return body;
    auto & fn = get_app_fn(dest);
    if (is_constant(fn)) {
        return mk_link(const_name(fn), body);
    } else {
        return body;
    }
}
template<class T>
auto pretty_fn<T>::pp_const(expr const & e, optional<unsigned> const & num_ref_univ_params) -> result {
    if (is_neutral_expr(e) && m_unicode)
        return T("◾");
    if (is_unreachable_expr(e) && m_unicode)
        return T("⊥");
    name n = const_name(e);
    if (m_notation && n == get_unit_star_name())
        return T("()");
    if (!num_ref_univ_params) {
        if (auto r = pp_local_ref(e))
            return *r;
    }
    // Remark: if num_ref_univ_params is "some", then it contains the number of
    // universe levels that are fixed in a section. That is, \c e corresponds to
    // a constant in a section which has fixed levels.
    auto short_n = n;
    if (!m_full_names) {
        if (auto it = is_aliased(n)) {
            if (!m_private_names || !hidden_to_user_name(m_env, n))
                short_n = *it;
        } else {
            for (name const & ns : get_namespaces(m_env)) {
                if (!ns.is_anonymous()) {
                    name new_n = n.replace_prefix(ns, name());
                    if (new_n != n &&
                        !new_n.is_anonymous() &&
                        (!new_n.is_atomic() || !is_protected(m_env, n))) {
                        short_n = new_n;
                        break;
                    }
                }
            }
        }
    }
    if (!m_private_names) {
        if (auto n1 = hidden_to_user_name(m_env, short_n))
            short_n = *n1;
    }
    if (m_ctx.has_local_pp_name(short_n.get_root())) {
        if (m_ctx.has_local_pp_name(n.get_root())) {
            n = get_root_tk() + n;
        }
    } else {
        n = short_n;
    }
    if (m_universes && !empty(const_levels(e))) {
        unsigned first_idx = 0;
        buffer<level> ls;
        to_buffer(const_levels(e), ls);
        if (num_ref_univ_params) {
            if (ls.size() <= *num_ref_univ_params)
                return result(escape(n));
            else
                first_idx = *num_ref_univ_params;
        }
        T r = compose(escape(n), T(".{"));
        bool first = true;
        for (unsigned i = first_idx; i < ls.size(); i++) {
            level const & l = ls[i];
            T l_fmt = pp_level(l);
            if (is_max(l) || is_imax(l))
                l_fmt = paren(l_fmt);
            if (first)
                r += nest(m_indent, l_fmt);
            else
                r += nest(m_indent, compose(line(), l_fmt));
            first = false;
        }
        r += T("}");
        return result(group(r));
    } else {
        return result(escape(n));
    }
}

static format pp_hole() { return format("{! !}"); }
template<class T>
auto pretty_fn<T>::pp_meta(expr const & e) -> result {
    if (m_use_holes) {
        return T(pp_hole());
    } else if (mlocal_name(e) != mlocal_pp_name(e)) {
        return result(T(mlocal_pp_name(e)));
    } else if (is_idx_metavar(e)) {
        return result(T((sstream() << "?x_" << to_meta_idx(e)).str()));
    } else if (is_metavar_decl_ref(e) && !m_purify_metavars) {
        return result(T((sstream() << "?m_" << get_metavar_decl_ref_suffix(e)).str()));
    } else if (m_purify_metavars) {
        return result(compose(T("?"), T(mlocal_name(e))));
    } else {
        return result(compose(T("?M."), T(mlocal_name(e))));
    }
}
template<class T>
auto pretty_fn<T>::pp_local(expr const & e) -> result {
    name n = sanitize_if_fresh(mlocal_pp_name(e));
    n = sanitize_name_generator_name(n);
    if (m_locals_full_names)
        return result(T("<") + T(n + mlocal_name(e)) + T(">"));
    else
        return T(escape(n));
}
template<class T>
bool pretty_fn<T>::has_implicit_args(expr const & f) {
    if (!closed(f) || m_preterm) {
        // The Lean type checker assumes expressions are closed.
        // If preterms are being processed, then we assume
        // there are no implicit arguments.
        return false;
    }
    try {
        expr type = m_ctx.relaxed_whnf(m_ctx.infer(f));
        push_local_fn push_local(m_ctx);
        while (is_pi(type)) {
            binder_info bi = binding_info(type);
            if (bi.is_implicit() || bi.is_strict_implicit() || bi.is_inst_implicit())
                return true;
            expr local = push_local(binding_name(type), binding_domain(type), binding_info(type));
            type = m_ctx.relaxed_whnf(instantiate(binding_body(type), local));
        }
        return false;
    } catch (exception &) {
        return false;
    }
}

static bool is_structure_instance(environment const & env, expr const & e, bool implicit) {
    expr const & fn = get_app_fn(e);
    if (!is_constant(fn)) return false;
    name const & mk_name = const_name(fn);
    if (!inductive::is_intro_rule(env, mk_name)) return false;
    name const & S       = mk_name.get_prefix();
    if (!is_structure(env, S)) return false;
    /* If implicit arguments is true, and the structure has parameters, we should not
       pretty print using { ... }, because we will not be able to see the parameters. */
    if (implicit && *inductive::get_num_params(env, S) > 0) return false;
    /* check whether it is a partially applied constructor application */
    if (get_app_num_args(e) != get_arity(env.get(mk_name).get_type())) return false;
    return true;
}
template<class T>
auto pretty_fn<T>::pp_structure_instance(expr const & e) -> result {
    lean_assert(is_structure_instance(m_env, e, m_implict));
    buffer<expr> args;
    expr const & mk = get_app_args(e, args);
    name const & S  = const_name(mk).get_prefix();
    unsigned num_params = *inductive::get_num_params(m_env, S);
    if (pp_using_anonymous_constructor(m_env, S)) {
        T r;
        for (unsigned i = num_params; i < args.size(); i++) {
            if (i > num_params) r += line();
            address_scope scope(*this, expr_address::app(args.size(), i));
            T fval_fmt     = pp(args[i]).fmt();
            if (i < args.size() - 1) fval_fmt += comma();
            r += fval_fmt;
        }
        r = group(nest(1, mk_link(const_name(mk), T("⟨")) + r + T("⟩")));
        return result(r);
    } else {
        auto fields = get_structure_fields(m_env, S);
        lean_assert(args.size() == num_params + fields.size());
        T r;
        if (m_structure_instances_qualifier)
            r += T(S) + space() + T(".");
        for (unsigned i = 0; i < fields.size(); i++) {
            if (i > 0 || m_structure_instances_qualifier) r += line();
            name fname          = fields[i];
            unsigned field_size = fname.utf8_size();
            unsigned arg_idx = i + num_params;
            address_scope scope(*this, expr_address::app(args.size(), arg_idx));
            T fval_fmt     = pp(args[arg_idx]).fmt();
            if (i < fields.size() - 1) fval_fmt += comma();
            r                  += mk_link(S + fname, T(fname)) + space() + *g_assign_fmt + space() + nest(field_size + 4, fval_fmt);
        }
        r = group(nest(1, mk_link(const_name(mk), T("{")) + r + T("}")));
        return result(r);
    }
}
template<class T>
bool pretty_fn<T>::is_field_notation_candidate(expr const & e) {
    if (!is_app(e)) return false;
    expr const & f = get_app_fn(e);
    if (!is_constant(f)) return false;
    name const & fn = const_name(f);
    if (!fn.is_string()) return false;
    if (pp_nodot(m_env, fn)) return false;
    name const & S = fn.get_prefix();
    /* The @ explicitness annotation cannot be combined with field notation, so fail on implicit args */
    if (m_implict && has_implicit_args(e)) return false;

    if (projection_info const * info = get_projection_info(m_env, const_name(f))) {
        if (get_app_num_args(e) == info->m_nparams + 1 &&
            /* If implicit arguments is true, and the structure has parameters, we should not
            pretty print using field notation because we will not be able to see the parameters. */
            (!m_implict || !info->m_nparams) &&
            /* We should not use field notation with type classes since the structure is implicit. */
            !is_class(m_env, S))
            return true;
    }

    if (m_generalized_field_notation) {
        if (!closed(e) || m_preterm) return false;

        if (!is_app_of(infer_type(app_arg(e)), S)) return false;

        auto fn_type = infer_type(f);
        auto num_args = get_app_num_args(e);
        for (unsigned i = 0; i + 1 < num_args; i++) {
            if (!is_pi(fn_type)) return false;
            if (is_explicit(binding_info(fn_type))) return false;
            fn_type = binding_body(fn_type);
        }

        if (!is_pi(fn_type)) return false;
        if (!is_explicit(binding_info(fn_type))) return false;
        if (!is_app_of(binding_domain(fn_type), S)) return false;

        return true;
    }
    return false;
}
template<class T>
auto pretty_fn<T>::pp_field_notation(expr const & e) -> result {
    buffer<expr> args;
    expr const & f   = get_app_args(e, args);
    bool ignore_hide = true;
    T s_fmt     = pp_child_at(args.back(), max_bp(), expr_address::app(args.size(), args.size() - 1), ignore_hide).fmt();
    return result(max_bp()+1, s_fmt + T(".") + mk_link(const_name(f), T(const_name(f).get_string())));
}
template<class T>
auto pretty_fn<T>::pp_app(expr const & e) -> result {
    if (auto r = pp_local_ref(e)) {
        return *r;
    }
    if (is_default_arg_app(e)) {
        return pp_child_at(app_fn(e), max_bp(), expr_address::fn());
    }
    expr const & fn = app_fn(e);
    if (m_structure_instances && is_structure_instance(m_env, e, m_implict)) {
        return pp_structure_instance(e);
    }
    if (m_structure_projections && is_field_notation_candidate(e)) {
        return pp_field_notation(e);
    }
    // If the application contains a metavariable, then we want to
    // show the function, otherwise it would be hard to understand the
    // context where the metavariable occurs. This is hack to implement
    // formatter.hide_full_terms
    bool ignore_hide = true;
    result res_fn    = pp_child_at(fn, max_bp()-1, expr_address::fn(), ignore_hide);
    T fn_fmt    = res_fn.fmt();
    if (m_implict && (!is_app(fn) || (is_local_ref(m_env, fn))) && has_implicit_args(fn)) {
        fn_fmt = compose(*g_explicit_fmt, fn_fmt);
    }
    result res_arg = pp_child_at(app_arg(e), max_bp(), expr_address::arg());
    return result(max_bp()-1, group(compose(fn_fmt, nest(m_indent, compose(line(), res_arg.fmt())))));
}
template<class T>
T pretty_fn<T>::pp_binder(expr const & local) {
    // [note] address is already set here
    T r;
    auto bi = local_info(local);
    if (bi != binder_info()) {
        r += T(open_binder_string(bi, m_unicode));
    }
    r += escape(mlocal_pp_name(local));
    if (m_binder_types) {
        r += space();
        r += compose(colon(), nest(m_indent, compose(line(), pp_child(mlocal_type(local), 0).fmt())));
    }
    if (bi != binder_info()) {
        r += T(close_binder_string(bi, m_unicode));
    }
    return r;
}
template<class T>
T pretty_fn<T>::pp_binder_block(buffer<name> const & names, expr const & type, binder_info const & bi) {
    T r;
    if (m_binder_types || bi != binder_info())
        r += T(open_binder_string(bi, m_unicode));
    for (name const & n : names) {
        r += escape(n);
        r += space();
    }
    if (m_binder_types) {
        r += compose(colon(), nest(m_indent, compose(line(), pp_child(type, 0).fmt())));
    }
    if (m_binder_types || bi != binder_info())
        r += T(close_binder_string(bi, m_unicode));
    return group(r);
}

template<class T>
T pretty_fn<T>::pp_binders(buffer<subexpr> const & locals) {
    unsigned num     = locals.size();
    buffer<name> names;
    expr local = locals[0].first;
    address la = locals[0].second;
    // [note] la points to the binder var type that made the local.
    expr   type      = mlocal_type(local);
    binder_info bi   = local_info(local);
    names.push_back(mlocal_pp_name(local));
    T r;
    for (unsigned i = 1; i < num; i++) {
        expr local = locals[i].first;
        address la = locals[i].second;
        address_scope scope(*this, la);
        if (!bi.is_inst_implicit() && mlocal_type(local) == type && local_info(local) == bi) {
            names.push_back(mlocal_pp_name(local));
        } else {
            r += group(compose(line(), pp_binder_block(names, type, bi)));
            names.clear();
            type = mlocal_type(local);
            bi   = local_info(local);
            names.push_back(mlocal_pp_name(local));
        }
    }
    address_scope scope(*this, la);
    r += group(compose(line(), pp_binder_block(names, type, bi)));
    return r;
}
template<class T>
auto pretty_fn<T>::pp_lambda(expr const & e) -> result {
    expr b = e;
    address adr;
    buffer<subexpr> locals;
    while (is_lambda(b)) {
        auto p = binding_body_fresh(b, true);
        locals.push_back(mk_pair(p.second, cons(expr_coord::lam_var_type, adr)));
        b = p.first;
        adr = cons(expr_coord::lam_body, adr);
    }
    T r = m_unicode ? *g_lambda_n_fmt : *g_lambda_fmt;
    r += pp_binders(locals);
    r += group(compose(comma(), nest(m_indent, compose(line(), pp_child_at(b, 0, adr).fmt()))));
    return result(0, r);
}

/** \brief Similar to #is_arrow, but only returns true if binder_info is the default one.
    That is, we don't want to lose binder info when pretty printing.
*/
static bool is_default_arrow(expr const & e) {
    return is_arrow(e) && binding_info(e) == binder_info();
}
template<class T>
auto pretty_fn<T>::pp_pi(expr const & e) -> result {
    if (is_default_arrow(e)) {
        result lhs = pp_child_at(binding_domain(e), get_arrow_prec(), expr_address::binding_type(e));
        expr   b   = lift_free_vars(binding_body(e), 1);
        address pb = expr_address::pi_body();
        result rhs = is_pi(b) ? pp_at(b, pb) : pp_child_at(b, get_arrow_prec() - 1, pb);
        T r   = group(lhs.fmt() + space() + (m_unicode ? *g_arrow_n_fmt : *g_arrow_fmt) + line() + rhs.fmt());
        return result(get_arrow_prec(), get_arrow_prec()-1, r);
    } else {
        expr b = e;
        address adr;
        buffer<subexpr> locals;
        while (is_pi(b) && !is_default_arrow(b)) {
            auto p = binding_body_fresh(b, true);
            locals.push_back(mk_pair(p.second, cons(expr_coord::pi_var_type, adr)));
            b = p.first;
            adr = cons(expr_coord::pi_body, adr);
        }
        T r;
        if (is_prop(b))
            r = m_unicode ? *g_forall_n_fmt : *g_forall_fmt;
        else
            r = m_unicode ? *g_pi_n_fmt : *g_pi_fmt;
        r += pp_binders(locals);
        r += group(compose(comma(), nest(m_indent, compose(line(), pp_child_at(b, 0, adr).fmt()))));
        return result(0, r);
    }
}

static bool is_have(expr const & e) {
    return is_app(e) && is_have_annotation(app_fn(e)) && is_binding(get_annotation_arg(app_fn(e)));
}
static bool is_show(expr const & e) {
    return is_show_annotation(e) && is_app(get_annotation_arg(e)) &&
        is_lambda(app_fn(get_annotation_arg(e)));
}
template<class T>
auto pretty_fn<T>::pp_have(expr const & e) -> result {
    // e = ( ANNOTATION { \la x : A, body  } ) $ ( proof ) = have x : A, from proof, body
    expr proof   = app_arg(e);
    expr binding = get_annotation_arg(app_fn(e));
    auto p       = binding_body_fresh(binding, true);
    expr local   = p.second;
    expr body    = p.first;
    name const & n = mlocal_pp_name(local);
    T type_fmt  = pp_child_at(mlocal_type(local), 0, expr_address::mlocal_type(local)).fmt();
    T proof_fmt = pp_child_at(proof, 0, expr_address::arg()).fmt();
    T body_fmt  = pp_child_at(body, 0, expr_address::lam_body()).fmt();
    T head_fmt  = *g_have_fmt;
    T r = head_fmt + space() + escape(n) + space();
    r += colon() + nest(m_indent, line() + type_fmt + comma() + space() + *g_from_fmt);
    r = group(r);
    r += nest(m_indent, line() + proof_fmt + comma());
    r = group(r);
    r += line() + body_fmt;
    return result(0, r);
}
template<class T>
auto pretty_fn<T>::pp_show(expr const & e) -> result {
    lean_assert(is_show(e));
    // e = annotation { (\la x, type) $ proof }
    expr s           = get_annotation_arg(e);
    expr proof       = app_arg(s);
    expr type        = binding_domain(app_fn(s));
    T type_fmt = pp_child_at(type, 0, append(expr_address::binding_type(app_fn(s)), expr_address::fn())).fmt();
    T proof_fmt = pp_child_at(proof, 0, expr_address::arg()).fmt();
    T r = *g_show_fmt + space() + nest(5, type_fmt) + comma() + space() + *g_from_fmt;
    r = group(r);
    r += nest(m_indent, compose(line(), proof_fmt));
    return result(0, group(r));
}
template<class T>
auto pretty_fn<T>::pp_explicit(expr const & e) -> result {
    result res_arg = pp_child(get_explicit_arg(e), max_bp());
    return result(max_bp(), compose(*g_explicit_fmt, res_arg.fmt()));
}
template<class T>
auto pretty_fn<T>::pp_delayed_abstraction(expr const & e) -> result {
    address_give_up_scope s(*this);
    if (m_use_holes) {
        return T(pp_hole());
    } else if (m_delayed_abstraction) {
        T r;
        r += T("[");
        buffer<name> ns; buffer<expr> es;
        get_delayed_abstraction_info(e, ns, es);
        for (unsigned i = 0; i < ns.size(); i++) {
            T r2;
            if (i) r2 += T(",") + line();
            r2 += pp(es[i]).fmt();
            r += group(r2);
        }
        r += T("]");
        return result(pp(get_delayed_abstraction_expr(e)).fmt() + nest(m_indent, r));
    } else {
        return pp(get_delayed_abstraction_expr(e));
    }
}
template<class T>
auto pretty_fn<T>::pp_equation(expr const & e) -> T {
    lean_assert(is_equation(e));
    // [todo] adding expression address information not implemented
    address_give_up_scope s(*this);
    T r = T("|");
    buffer<expr> args;
    get_app_args(equation_lhs(e), args);
    for (expr const & arg : args) {
        r += space() + pp_child(arg, max_bp()).fmt();
    }
    r += space() + *g_assign_fmt + space() + pp_child(equation_rhs(e), 0).fmt();
    return r;
}
template<class T>
auto pretty_fn<T>::pp_equations(expr const & e) -> optional<result> {
    // [todo] adding expression address information for equations not implemented
    address_give_up_scope s(*this);
    buffer<expr> eqns;
    unsigned num_fns = equations_num_fns(e);
    to_equations(e, eqns);
    buffer<expr> fns;
    expr eqn = eqns[0];
    for (unsigned i = 0; i < num_fns; i++) {
        if (!is_lambda(eqn)) return optional<result>();
        if (!closed(binding_domain(eqn))) return optional<result>();
        auto p = binding_body_fresh(eqn, true);
        fns.push_back(p.second);
        eqn = p.first;
    }
    T r;
    if (num_fns > 1) {
        r = T("mutual_def") + space();
        for (unsigned i = 0; i < num_fns; i++) {
            if (i > 0) r += T(", ");
            r += pp(fns[i]).fmt();
        }
        r += line();
    } else {
        r = T("def") + space() + pp(fns[0]).fmt() + space() + colon() + space() + pp(mlocal_type(fns[0])).fmt();
    }
    unsigned eqnidx = 0;
    for (unsigned fidx = 0; fidx < num_fns; fidx++) {
        if (num_fns > 1) {
            if (fidx > 0) r += line();
            r += T("with") + space() + pp(fns[fidx]).fmt() + space() + colon() +
                space() + pp(mlocal_type(fns[fidx])).fmt();
        }
        if (eqnidx >= eqns.size()) return optional<result>();
        expr eqn = eqns[eqnidx];
        while (is_lambda(eqn)) {
            eqn = binding_body_fresh(eqn, true).first;
        }
        eqnidx++;
        if (is_equation(eqn)) {
            r += line() + pp_equation(eqn);
            while (eqnidx < eqns.size()) {
                expr eqn = eqns[eqnidx];
                while (is_lambda(eqn)) {
                    eqn = binding_body_fresh(eqn, true).first;
                }
                if (is_equation(eqn) &&
                    get_app_fn(equation_lhs(eqn)) == fns[fidx]) {
                    r += line() + pp_equation(eqn);
                    eqnidx++;
                } else {
                    break;
                }
            }
        } else {
            /* noequation */
            r += line() + T("[none]");
        }
    }
    if (eqns.size() != eqnidx) return optional<result>();
    return optional<result>(r);
}
template<class T>
auto pretty_fn<T>::pp_macro_default(expr const & e) -> result {
    // TODO(Leo): have macro annotations
    // fix macro<->pp interface
    // [note] address information not supported for macros.
    address_give_up_scope s(*this);
    if (is_prenum(e)) {
        return T(prenum_value(e).to_string());
    }
    T r = compose(T("["), T(macro_def(e).get_name()));
    for (unsigned i = 0; i < macro_num_args(e); i++)
        r += nest(m_indent, compose(line(), pp_child(macro_arg(e, i), max_bp()).fmt()));
    r += T("]");
    return result(group(r));
}
template<class T>
auto pretty_fn<T>::pp_macro(expr const & e) -> result {
    // [note] address information not supported for macros.
    address_give_up_scope s(*this);
    if (is_explicit(e)) {
        return pp_explicit(e);
    } else if (is_expr_quote(e)) {
        return result(T("`(") + nest(4, pp(get_expr_quote_value(e)).fmt()) + T(")"));
    } else if (is_pexpr_quote(e)) {
        return result(T("``(") + nest(2, pp(get_pexpr_quote_value(e)).fmt()) + T(")"));
    } else if (is_delayed_abstraction(e)) {
        return pp_delayed_abstraction(e);
    } else if (is_inaccessible(e)) {
        T r = T(".") + pp_child(get_annotation_arg(e), max_bp()).fmt();
        return result(r);
    } else if (is_as_pattern(e)) {
        auto lhs_fmt = pp_child(get_as_pattern_lhs(e), max_bp()).fmt();
        auto rhs_fmt = pp_child(get_as_pattern_rhs(e), max_bp()).fmt();
        return result(lhs_fmt + T("@") + rhs_fmt);
    } else if (is_pattern_hint(e)) {
        return result(group(nest(2, T("(:") + pp(get_pattern_hint_arg(e)).fmt() + T(":)"))));
    } else if (is_marked_as_comp_irrelevant(e)) {
        if (m_hide_comp_irrel)
            return m_unicode ? T("◾") : T("irrel");
        else
            return pp(get_annotation_arg(e));
    } else if (!m_strings && to_string(e)) {
        expr n = *macro_def(e).expand(e, m_ctx);
        return pp(n);
    } else if (is_equations(e)) {
        if (auto r = pp_equations(e))
            return *r;
        else
            return pp_macro_default(e);
    } else if (is_annotation(e)) {
        if (m_annotations)
            return T("[") + T(get_annotation_kind(e)) + space() + pp(get_annotation_arg(e)).fmt() + T("]");
        else
            return pp(get_annotation_arg(e));
    } else if (is_rec_fn_macro(e)) {
        return T("[") + T(get_rec_fn_name(e)) + T("]");
    } else if (is_synthetic_sorry(e)) {
        if (m_use_holes)
            return T(pp_hole());
        else
            return m_unicode ? T("⁇") : T("??");
    } else if (is_sorry(e)) {
        if (m_use_holes)
            return T(pp_hole());
        else
            return T("sorry");
    } else {
        return pp_macro_default(e);
    }
}
template<class T>
auto pretty_fn<T>::pp_let(expr e) -> result {
    buffer<std::tuple<expr, expr, expr>> decls;
    while (true) {
        expr t   = let_type(e);
        expr v   = let_value(e);
        expr b   = let_body(e);
        auto p   = let_body_fresh(e, true);
        decls.emplace_back(p.second, t, v);
        e        = p.first;
        if (!is_let(e))
            break;
    }
    lean_assert(!decls.empty());
    T r    = *g_let_fmt;
    unsigned sz = decls.size();
    for (unsigned i = 0; i < sz; i++) {
        expr l, t, v;
        std::tie(l, t, v) = decls[i];
        address base = expr_address::repeat(address(expr_coord::elet_body), i);
        name const & n = mlocal_pp_name(l);
        T beg     = i == 0 ? space() : line();
        T sep     = i < sz - 1 ? comma() : T();
        T entry   = T(n);
        T v_fmt   = pp_child_at(v, 0, cons(expr_coord::elet_assignment, base)).fmt();
        if (is_neutral_expr(t)) {
            entry += space() + *g_assign_fmt + nest(m_indent, line() + v_fmt + sep);
        } else {
            T t_fmt   = pp_child_at(t, 0, cons(expr_coord::elet_var_type, base)).fmt();
            entry += space() + colon() + space() + t_fmt + space() + *g_assign_fmt + nest(m_indent, line() + v_fmt + sep);
        }
        r += nest(3 + 1, beg + group(entry));
    }
    T b = pp_child_at(e, 0, expr_address::repeat(address(expr_coord::elet_body), sz)).fmt();
    r += line() + *g_in_fmt + space() + nest(2 + 1, b);
    return result(0, r);
}
template<class T>
auto pretty_fn<T>::pp_num(mpz const & n, unsigned bp) -> result {
    if (n.is_neg()) {
        auto prec = get_expr_precedence(m_token_table, "-");
        if (!prec || bp > *prec) {
            return result(paren(T(n.to_string())));
        }
    }
    return result(T(n.to_string()));
}

// Return the number of parameters in a notation declaration.
static unsigned get_num_parameters(notation_entry const & entry) {
    if (entry.is_numeral())
        return 0;
    unsigned r = 0;
    if (!entry.is_nud())
        r++;
    for (auto const & t : entry.get_transitions()) {
        switch (t.get_action().kind()) {
        case notation::action_kind::Skip:
        case notation::action_kind::Binder:
        case notation::action_kind::Binders:
            break;
        case notation::action_kind::Expr:
        case notation::action_kind::Exprs:
        case notation::action_kind::ScopedExpr:
        case notation::action_kind::Ext:
            r++;
        }
    }
    return r;
}
template<class T>
bool pretty_fn<T>::match(level const & p, level const & l) {
    if (p == l)
        return true;
    if (m_universes)
        return false;
    if (is_placeholder(p))
        return true;
    if (is_succ(p) && is_succ(l))
        return match(succ_of(p), succ_of(l));
    return false;
}
template<class T>
bool pretty_fn<T>::match(expr const & p, subexpr const & e, buffer<optional<subexpr>> & args) {
    if (is_explicit(p)) {
        return match(get_explicit_arg(p), e, args);
    } else if (is_as_atomic(p)) {
        return match(get_app_fn(get_as_atomic_arg(p)), e, args);
    } else if (is_var(p)) {
        unsigned vidx = var_idx(p);
        if (vidx >= args.size())
            return false;
        unsigned i = args.size() - vidx - 1;
        if (args[i])
            return *args[i] == e;
        args[i] = e;
        return true;
    } else if (is_placeholder(p)) {
        return true;
    } else if (is_constant(p) && is_constant(e.first)) {
        if (const_name(p) != const_name(e.first))
            return false;
        levels p_ls = const_levels(p);
        levels e_ls = const_levels(p); // [note] is this a bug!?
        while (!is_nil(p_ls)) {
            if (is_nil(e_ls))
                return false; // e must have at least as many arguments as p
            if (!match(head(p_ls), head(e_ls)))
                return false;
            p_ls = tail(p_ls);
            e_ls = tail(e_ls);
        }
        return true;
    } else if (is_sort(p)) {
        if (!is_sort(e.first))
            return false;
        return match(sort_level(p), sort_level(e.first));
    } else if (is_app(e.first)) {
        buffer<expr> p_args, e_args;
        expr p_fn    = get_app_args(p, p_args);
        expr e_fn    = get_app_args(e.first, e_args);
        address e_fn_adr = append(expr_address::fn(e_args.size()), e.second);
        if (!match(p_fn, mk_pair(e_fn, e_fn_adr), args))
            return false;
        if (is_explicit(p)) {
            if (p_args.size() != e_args.size())
                return false;
            for (unsigned i = 0; i < p_args.size(); i++) {
                auto ea = mk_pair(e_args[i], append(expr_address::app(e_args.size(), i), e.second));
                if (!match(p_args[i], ea, args))
                    return false;
            }
            return true;
        } else {
            try {
                expr fn_type = m_ctx.infer(e_fn);
                unsigned j = 0;
                for (unsigned i = 0; i < e_args.size(); i++) {
                    fn_type = m_ctx.relaxed_whnf(fn_type);
                    if (!is_pi(fn_type))
                        return false;
                    expr const & body        = binding_body(fn_type);
                    binder_info const & info = binding_info(fn_type);
                    if (is_explicit(info)) {
                        if (j >= p_args.size())
                            return false;
                        auto ea = mk_pair(e_args[i], append(expr_address::app(e_args.size(), i), e.second));
                        if (!match(p_args[j], ea, args))
                            return false;
                        j++;
                    }
                    fn_type = instantiate(body, e_args[i]);
                }
                return j == p_args.size();
            } catch (exception &) {
                return false;
            }
        }
    } else {
        return false;
    }
}

static unsigned get_some_precedence(token_table const & t, name const & tk) {
    if (tk.is_atomic() && tk.is_string()) {
        if (auto p = get_expr_precedence(t, tk.get_string()))
            return *p;
    } else {
        if (auto p = get_expr_precedence(t, tk.to_string_unescaped().c_str()))
            return *p;
    }
    return 0;
}

template<class T>
auto pretty_fn<T>::tag(address const & a, expr const & e, result const & r) -> result {
    T t = r.fmt();
    t = tag(a, e, t);
    return r.with(t);
}

template<class T>
auto pretty_fn<T>::pp_notation_child(expr const & e, unsigned rbp, unsigned lbp) -> result {
    if (is_app(e)) {
        if (m_numerals) {
            if (auto n = to_num(e)){
                address_reset_scope ars(*this);
                return tag(ars.m_adr, e, pp_num(*n, lbp));
            }
        }
        if (m_strings) {
            if (auto r = to_string(e))      return tag(m_address, e, T(pp_string_literal(*r)));
            if (auto r = to_char(m_ctx, e)) return tag(m_address, e, T(pp_char_literal(*r)));
        }
        expr const & f = app_fn(e);
        if (is_implicit(f)) {
            address_scope s(*this, expr_address::fn());
            return pp_notation_child(f, rbp, lbp);
        } else if (!m_coercion && is_coercion(e)) {
            return pp_hide_coercion(e, rbp);
        } else if (!m_coercion && is_coercion_fn(e)) {
            return pp_hide_coercion_fn(e, rbp);
        }
    }
    result r = pp(e);
    /* see invariants of `pretty_fn::result`: Check that the surrounding notation would parse at least r
     * by the first invariant, and at most r (instead of the following token with binding power lbp) by the
     * second invariant. */
    if (rbp < r.lbp() && r.rbp() >= lbp) {
        return r;
    } else {
        return result(paren(r.fmt()));
    }
}

static bool is_atomic_notation(notation_entry const & entry) {
    if (!entry.is_nud())
        return false;
    list<notation::transition> const & ts = entry.get_transitions();
    if (!is_nil(tail(ts)))
        return false;
    return head(ts).get_action().kind() == notation::action_kind::Skip;
}

template<class T>
static T mk_tk_fmt(name const & tkn) {
    auto tk = tkn.to_string_unescaped();
    if (!tk.empty() && tk.back() == ' ') {
        tk.pop_back();
        return T(tk) + line();
    } else {
        return T(tk);
    }
}
template<class T>
auto pretty_fn<T>::pp_notation(notation_entry const & entry, buffer<optional<subexpr>> & args) -> optional<result> {
    if (entry.is_numeral()) {
        return some(result(T(entry.get_num().to_string())));
    } else if (is_atomic_notation(entry)) {
        T fmt   = mk_link(entry.get_expr(), T(head(entry.get_transitions()).get_token().to_string_unescaped()));
        return some(result(fmt));
    } else {
        using notation::transition;
        buffer<transition> ts;
        buffer<subexpr> locals; // from scoped_expr
        to_buffer(entry.get_transitions(), ts);
        T fmt;
        unsigned i         = ts.size();
        // bp of the last action
        unsigned last_rbp  = inf_bp()-1;
        // bp of the token immediately to the right of the action
        unsigned token_lbp = 0;
        bool last          = true;
        while (i > 0) {
            --i;
            T curr;
            notation::action const & a = ts[i].get_action();
            name const & tk = ts[i].get_token();
            T tk_fmt = mk_link(entry.get_expr(), mk_tk_fmt<T>(ts[i].get_pp_token().to_string_unescaped()));
            switch (a.kind()) {
            case notation::action_kind::Skip:
                curr = tk_fmt;
                if (last)
                    // invariant fulfilled: Skip action will never parse a trailing token
                    last_rbp = inf_bp();
                break;
            case notation::action_kind::Expr:
                if (args.empty() || !args.back()) {
                    return optional<result>();
                } else {
                    auto ea = *args.back();
                    expr e = ea.first;
                    address e_adr = ea.second;
                    args.pop_back();
                    address_scope s(*this, e_adr);
                    result e_r   = pp_notation_child(e, a.rbp(), token_lbp);
                    curr = tk_fmt + e_r.fmt();
                    if (last)
                        /* last_rbp can be no more than `a.rbp()`, since this is the bp used during parsing.
                         * However, `e_r.rbp()` may actually be smaller since it may be missing parentheses
                         * compared to the original input. For example, when re-printing `x >>= (fun y, z) = ...`,
                         * `e_r.fmt()` will be `fun y, z`. If we used the rbp of the `>>=` instead of
                         * `e_r.rbp()` (0), we would get the wrong output `x >>= fun y, z = ...`. */
                        last_rbp = std::min(a.rbp(), e_r.rbp());
                    break;
                }
            case notation::action_kind::Exprs:
                if (args.empty() || !args.back()) {
                    return optional<result>();
                } else {
                    auto e = *args.back();
                    args.pop_back();
                    expr const & rec = a.get_rec();
                    optional<expr> const & ini = a.get_initial();
                    buffer<subexpr> rec_args;
                    bool matched_once = false;
                    while (true) {
                        args.resize(args.size() + 2);
                        if (!match(rec, e, args)) {
                            args.pop_back();
                            args.pop_back();
                            break;
                        }
                        optional<subexpr> new_e = args.back();
                        args.pop_back();
                        optional<subexpr> rec_arg = args.back();
                        args.pop_back();
                        if (!new_e || !rec_arg)
                            return optional<result>();
                        rec_args.push_back(*rec_arg);
                        e = *new_e;
                        matched_once = true;
                    }
                    if (!matched_once && ini)
                        return optional<result>();
                    if (ini) {
                        if (!match(*ini, e, args))
                            return optional<result>();
                    } else {
                        rec_args.push_back(e);
                    }
                    if (!a.is_fold_right())
                        std::reverse(rec_args.begin(), rec_args.end());
                    unsigned curr_lbp = token_lbp;
                    if (auto t = a.get_terminator()) {
                        curr = T(t->to_string_unescaped());
                        curr_lbp = get_some_precedence(m_token_table, *t);
                    }
                    unsigned j       = rec_args.size();
                    T sep_fmt   = T(a.get_sep().to_string_unescaped());
                    unsigned sep_lbp = get_some_precedence(m_token_table, a.get_sep());
                    while (j > 0) {
                        --j;
                        auto ra = rec_args[j];
                        address_scope s(*this, ra.second);
                        result arg_res = pp_notation_child(ra.first, a.rbp(), curr_lbp);
                        if (j == 0) {
                            curr = tk_fmt + arg_res.fmt() + curr;
                        } else {
                            curr = sep_fmt + arg_res.fmt() + curr;
                        }
                        curr_lbp = sep_lbp;
                    }
                    break;
                }
            case notation::action_kind::Binder: {
                if (locals.size() != 1)
                    return optional<result>();
                subexpr l = locals[0];
                curr = tk_fmt + pp_binder_at(l.first, l.second);
                break; }
            case notation::action_kind::Binders:
                curr = tk_fmt + pp_binders(locals);
                break;
            case notation::action_kind::ScopedExpr:
                if (args.empty() || !args.back()) {
                    return optional<result>();
                } else {
                    auto e            = *args.back();
                    bool first_scoped = locals.empty();
                    unsigned i = 0;
                    args.pop_back();
                    expr const & rec = a.get_rec();
                    while (true) {
                        args.resize(args.size() + 1);
                        if (!match(rec, e, args) || !args.back()) {
                            args.pop_back();
                            break;
                        }
                        auto b = *args.back();
                        args.pop_back();
                        if (!((is_lambda(b.first) && a.use_lambda_abstraction()) ||
                              (is_pi(b.first) && !a.use_lambda_abstraction()))) {
                            break;
                        }
                        expr_pair p = binding_body_fresh(b.first, true);
                        if (first_scoped) {
                            locals.push_back(mk_pair(p.second, append(expr_address::binding_type(b.first), b.second)));
                        } else {
                            if (i >= locals.size() || locals[i].first != p.second)
                                return optional<result>();
                        }
                        e.first = p.first;
                        e.second = append(expr_address::binding_body(b.first), b.second);
                        i++;
                    }
                    if (locals.empty())
                        return optional<result>();
                    address_scope s(*this, e.second);
                    result e_r   = pp_notation_child(e.first, a.rbp(), token_lbp);
                    curr = tk_fmt + e_r.fmt();
                    if (last)
                        // see Expr action
                        last_rbp = std::min(a.rbp(), e_r.rbp());
                    break;
                }
            case notation::action_kind::Ext:
                return optional<result>();
            }
            token_lbp = get_some_precedence(m_token_table, tk);
            if (last) {
                fmt = curr;
                last = false;
            } else {
                fmt = curr + fmt;
            }
        }
        unsigned first_lbp = inf_bp();
        if (!entry.is_nud()) {
            first_lbp = token_lbp;
            lean_assert(!last);
            if (args.size() != 1 || !args.back())
                return optional<result>();
            auto e = *args.back();
            args.pop_back();
            address_scope s(*this, e.second);
            T e_fmt = pp_notation_child(e.first, 0, token_lbp).fmt();
            fmt = e_fmt + fmt;
        }
        return optional<result>(result(first_lbp, last_rbp, group(nest(m_indent, fmt))));
    }
}
template<class T>
auto pretty_fn<T>::pp_notation(subexpr const & ep) -> optional<result> {
    expr e = ep.first;
    if (!m_notation || is_var(e))
        return optional<result>();
    for (notation_entry const & entry : get_notation_entries(m_env, head_index(e))) {
        if (entry.group() == notation_entry_group::Reserve)
            continue;
        if (!m_unicode && !entry.is_safe_ascii())
            continue; // ignore this notation declaration since unicode support is not enabled
        unsigned num_params = get_num_parameters(entry);
        buffer<optional<subexpr>> args;
        args.resize(num_params);
        if (match(entry.get_expr(), ep, args)) {
            if (auto r = pp_notation(entry, args))
                return r;
        }
    }
    return optional<result>();
}

static bool is_pp_atomic(expr const & e) {
    switch (e.kind()) {
    case expr_kind::App:
    case expr_kind::Lambda:
    case expr_kind::Pi:
    case expr_kind::Macro:
        return false;
    default:
        return true;
    }
}

static bool is_subtype(expr const & e) {
    return
        is_constant(get_app_fn(e), get_subtype_name()) &&
        get_app_num_args(e) == 2 &&
        is_lambda(app_arg(e));
}
template<class T>
auto pretty_fn<T>::pp_subtype(expr const & e) -> result {
    lean_assert(is_subtype(e));
    expr pred = app_arg(e);
    lean_assert(is_lambda(pred));
    auto p     = binding_body_fresh(pred, true);
    expr body  = p.first;
    expr local = p.second;
    T f_body = pp_child_at(body, 0, {expr_coord::lam_body, expr_coord::app_arg}).fmt();
    T r   = bracket("{", T(mlocal_pp_name(local)) + space() + T("//") + space() + f_body, "}");
    return result(r);
}

static bool is_emptyc(expr const & e) {
    return
        is_constant(get_app_fn(e), get_has_emptyc_emptyc_name()) &&
        get_app_num_args(e) == 2;
}

static bool is_singleton(expr const & e) {
    return
        is_constant(get_app_fn(e), get_has_singleton_singleton_name()) &&
        get_app_num_args(e) == 4;
}

static bool is_insert(expr const & e) {
    return
        is_constant(get_app_fn(e), get_has_insert_insert_name()) &&
        get_app_num_args(e) == 5;
}

/* Return true iff 'e' encodes a nonempty finite collection,
   and stores its elements at elems. */
static bool is_explicit_collection(expr const & ex, buffer<subexpr> & elems) {
    expr e = ex;
    address adr;
    while (true) {
        if (is_emptyc(e)) {
            return true;
        } else if (is_singleton(e)) {
            elems.push_back(mk_pair(app_arg(e), cons(expr_coord::app_arg, adr)));
            return true;
        } else if (is_insert(e)) {
            elems.push_back(mk_pair(app_arg(app_fn(e)), cons(expr_coord::app_arg, cons(expr_coord::app_fn, adr))));
            e = app_arg(e);
            adr = cons(expr_coord::app_arg, adr);
        } else {
            return false;
        }
    }
}
template<class T>
auto pretty_fn<T>::pp_explicit_collection(buffer<subexpr> const & elems) -> result {
    if (elems.empty()) {
        return result(T(m_unicode ? "∅" : "{}"));
    } else {
        subexpr elem = elems[elems.size() - 1];
        T r = pp_child_at(elem.first, 0, elem.second).fmt();
        for (unsigned i = elems.size() - 1; i > 0;) {
            --i;
            elem = elems[i];
            r += nest(m_indent, comma() + line() + pp_child_at(elem.first, 0, elem.second).fmt());
        }
        r = group(bracket("{", r, "}"));
        return result(r);
    }
}

bool is_set_of(expr const & e) {
    return
        is_constant(get_app_fn(e), get_set_of_name()) &&
        get_app_num_args(e) == 2 &&
        is_lambda(app_arg(e));
}
template<class T>
auto pretty_fn<T>::pp_set_of(expr const & e) -> result {
    lean_assert(is_set_of(e));
    expr pred = app_arg(e);
    lean_assert(is_lambda(pred));
    auto p     = binding_body_fresh(pred, true);
    expr body  = p.first;
    expr local = p.second;
    T ppb = pp_binder_at(local, {expr_coord::lam_var_type, expr_coord::app_arg});
    T r   = bracket("{",
                         ppb + space() + T("|") + space() +
                         pp_child_at(body, 0, {expr_coord::lam_body, expr_coord::app_arg}).fmt(), "}");
    return result(r);
}

static bool is_sep(expr const & e) {
    return
        is_constant(get_app_fn(e), get_has_sep_sep_name()) &&
        get_app_num_args(e) == 5 &&
        is_lambda(app_arg(app_fn(e)));
}
template<class T>
auto pretty_fn<T>::pp_sep(expr const & e) -> result {
    lean_assert(is_sep(e));
    expr s    = app_arg(e);
    T pps = pp_child_at(s, 0, address(expr_coord::app_arg)).fmt();
    expr pred = app_arg(app_fn(e));
    lean_assert(is_lambda(pred));
    auto p     = binding_body_fresh(pred, true);
    expr body  = p.first;
    T ppbody = pp_child_at(body, 0, {expr_coord::lam_body, expr_coord::app_arg, expr_coord::app_fn}).fmt();
    expr local = p.second;
    T in  = T(m_unicode ? "∈" : "in");
    T r   = bracket("{",
                         T(mlocal_pp_name(local)) + space() + in + space() +
                         pps + space() + T("|") + space() + ppbody, "}");
    return result(r);
}
template<class T>
auto pretty_fn<T>::pp_prod(expr const & e) -> result {
    T r = pp_at(app_arg(app_fn(e)), {expr_coord::app_arg, expr_coord::app_fn}).fmt();
    auto it = app_arg(e);
    address adr;
    adr = cons(expr_coord::app_arg, adr);
    while (is_app_of(it, get_prod_mk_name(), 4)) {
        r += comma() + line();
        r += pp_at(app_arg(app_fn(it)), append({expr_coord::app_arg, expr_coord::app_fn}, adr)).fmt();
        it = app_arg(it);
        adr = cons(expr_coord::app_arg, adr);
    }
    r += comma() + line();
    r += pp_at(it, adr).fmt();
    return result(paren(group(r)));
}
template<class T>
auto pretty_fn<T>::pp_at(expr const & e, address local_address, bool ignore_hide) -> result {
    address_scope scope(*this, local_address);
    return  pp(e, ignore_hide);
}
template<class T>
auto pretty_fn<T>::pp_child_at(expr const & e, unsigned bp, address local_address, bool ignore_hide, bool below_implicit) -> result {
     address_scope scope(*this, local_address);
     return pp_child(e, bp, ignore_hide, below_implicit);
}
template<class T>
T pretty_fn<T>::pp_binder_at(expr const & local, address local_address) {
     address_scope scope(*this, local_address);
     return pp_binder(local);
}
template<class T>
auto pretty_fn<T>::pp(expr const & e, bool ignore_hide) -> result {
    address_reset_scope ars(*this);
    result r = tag(ars.m_adr, e, pp_core(e, ignore_hide));
    return r;
}
template<class T>
auto pretty_fn<T>::pp_core(expr const & e, bool ignore_hide) -> result {
    check_system("pretty printer");
    if ((m_depth >= m_max_depth ||
         m_num_steps > m_max_steps ||
         (m_hide_full_terms && !ignore_hide && !has_expr_metavar(e))) &&
        !is_pp_atomic(e)) {
        return result(m_unicode ? *g_ellipsis_n_fmt : *g_ellipsis_fmt);
    }
    flet<unsigned> let_d(m_depth, m_depth+1);
    m_num_steps++;

    if (m_numerals) {
        if (auto n = to_num(e)) return pp_num(*n, 0);
    }
    if (m_strings) {
        if (auto r = to_string(e))      return T(pp_string_literal(*r));
        if (auto r = to_char(m_ctx, e)) return T(pp_char_literal(*r));
    }
    try {
        if (!m_proofs && !is_constant(e) && !is_mlocal(e) && closed(e) && is_prop(m_ctx.infer(e))) {
            return result(T("_"));
        }
    } catch (exception &) {}

    if (auto r = pp_notation(mk_pair(e, address())))
        return *r;

    if (m_notation) {
        if (is_subtype(e))
            return pp_subtype(e);
        if (is_sep(e))
            return pp_sep(e);
        if (is_set_of(e))
            return pp_set_of(e);
        buffer<subexpr> elems;
        if (is_explicit_collection(e, elems)) {
            std::reverse(elems.begin(), elems.end());
            return pp_explicit_collection(elems);
        }

        if (is_app_of(e, get_prod_mk_name(), 4))
            return pp_prod(e);
    }

    if (is_placeholder(e))  return result(*g_placeholder_fmt);
    if (is_show(e))         return pp_show(e);
    if (is_have(e))         return pp_have(e);
    if (is_typed_expr(e))   return pp(get_typed_expr_expr(e));
    if (m_num_nat_coe)
        if (auto k = to_unsigned(e))
            return T(format(*k));
    switch (e.kind()) {
    case expr_kind::Var:       return pp_var(e);
    case expr_kind::Sort:      return pp_sort(e);
    case expr_kind::Constant:  return mk_link(const_name(e), pp_const(e));
    case expr_kind::Meta:      return pp_meta(e);
    case expr_kind::Local:     return pp_local(e);
    case expr_kind::App:       return pp_app(e);
    case expr_kind::Lambda:    return pp_lambda(e);
    case expr_kind::Pi:        return pp_pi(e);
    case expr_kind::Macro:     return pp_macro(e);
    case expr_kind::Let:       return pp_let(e);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}
template<class T>
pretty_fn<T>::pretty_fn(environment const & env, options const & o, abstract_type_context & ctx):
    m_env(env), m_ctx(ctx), m_token_table(get_token_table(env)) {
    set_options_core(o);
    m_meta_prefix   = "M";
    m_next_meta_idx = 1;
    m_address_give_up = false;
}
template lean::pretty_fn<lean::eformat>::pretty_fn(lean::environment const&, lean::options const&, lean::abstract_type_context&);

// Custom beta reduction procedure for the pretty printer.
// We don't want to reduce application in show annotations.
class pp_beta_reduce_fn : public replace_visitor {
    virtual expr visit_meta(expr const & e) override { return e; }
    virtual expr visit_local(expr const & e) override { return e; }

    virtual expr visit_macro(expr const & e) override {
        if (is_show_annotation(e) && is_app(get_annotation_arg(e))) {
            expr const & n = get_annotation_arg(e);
            expr new_fn  = visit(app_fn(n));
            expr new_arg = visit(app_arg(n));
            return mk_show_annotation(mk_app(new_fn, new_arg));
        } else {
            return replace_visitor::visit_macro(e);
        }
    }

    virtual expr visit_app(expr const & e) override {
        expr new_e = replace_visitor::visit_app(e);
        if (is_head_beta(new_e))
            return visit(head_beta_reduce(new_e));
        else
            return new_e;
    }
};

std::string sexpr_to_string(sexpr const & s) {
    if (is_string(s))
        return to_string(s);
    std::stringstream ss;
    ss << s;
    return ss.str();
}

// check whether a space must be inserted between the strings so that lexing them would
// produce separate tokens
template<class T>
std::pair<bool, token_table const *> pretty_fn<T>::needs_space_sep(token_table const * last, std::string const & s1, std::string const & s2) const {
    if (s1.empty() || (is_id_rest(get_utf8_last_char(s1.data()), s1.data() + s1.size()) && is_id_rest(s2.data(), s2.data() + s2.size())))
        return mk_pair(true, nullptr); // would be lexed as a single identifier without space

    if (last) {
        // complete deferred two-token lookahead
        for (char c : s2) {
            last = last->find(c);
            if (!last)
                break;
            if (last->value())
                return mk_pair(true, nullptr);
        }
        if (last) {
            // would need an even larger lookahead, give up
            return mk_pair(true, nullptr);
        }
    }

    // check whether s1 + s2 has a longer prefix in the token table than s1
    token_table const * t = &m_token_table;
    for (char c : s1) {
        t = t->find(c);
        if (!t)
            return mk_pair(false, nullptr); // s1 must be an identifier, and we know s2 does not start with is_id_rest
    }
    for (char c : s2) {
        t = t->find(c);
        if (!t)
            return mk_pair(false, nullptr);
        if (t->value())
            return mk_pair(true, nullptr);
    }

    // the next identifier may expand s1 + s2 to a token, defer decision
    return mk_pair(false, t);
}
template<class T>
T pretty_fn<T>::operator()(expr const & e) {
    auto purified = purify(m_beta ? pp_beta_reduce_fn()(e) : e);

    if (!m_options.contains(get_pp_proofs_name()) && !get_pp_all(m_options)) {
        try {
            m_proofs = !closed(purified) || is_prop(m_ctx.infer(purified));
        } catch (exception &) {
            m_proofs = true;
        }
    }

    m_depth = 0; m_num_steps = 0;
    result r = pp_child(purified, 0);

    return r.fmt();
}
template eformat lean::pretty_fn<lean::eformat>::operator()(lean::expr const&);


formatter_factory mk_pretty_formatter_factory() {
    return [](environment const & env, options const & o, abstract_type_context & ctx) { // NOLINT
        auto fn_ptr = std::make_shared<plain_pretty_fn>(env, o, ctx);
        return formatter(o, [=](expr const & e, options const & new_o) {
                fn_ptr->set_options(new_o);
                auto res = (*fn_ptr)(e);
                // insert spaces so that lexing the result round-trips
                std::function<bool(sexpr const &, sexpr const &)> sep; // NOLINT
                token_table const * last = nullptr;
                sep = [&](sexpr const & s1, sexpr const & s2) {
                    auto p = fn_ptr->needs_space_sep(last, sexpr_to_string(s1), sexpr_to_string(s2));
                    last = p.second;
                    return p.first;
                };
                return res.separate_tokens(sep);
            });
    };
}

static options mk_options(bool detail) {
    options opts;
    if (detail) {
        opts = opts.update(name{"pp", "implicit"}, true);
        opts = opts.update(name{"pp", "notation"}, false);
    }
    return opts;
}

static void pp_core(environment const & env, expr const & e, bool detail) {
    type_checker tc(env);
    io_state ios(mk_pretty_formatter_factory(), mk_options(detail));
    regular(env, ios, tc) << e << "\n";
}
}

// for debugging purposes
void pp(lean::environment const & env, lean::expr const & e) { lean::pp_core(env, e, false); }
void pp_detail(lean::environment const & env, lean::expr const & e) { lean::pp_core(env, e, true); }
