/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "checker/simple_pp.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/for_each_fn.h"

namespace lean {

format compose_many(std::initializer_list<format> const & fmts) {
    format res;
    bool first = true;
    for (auto & fmt : fmts) {
        if (first) {
            res = fmt;
            first = false;
        } else {
            res = compose(res, fmt);
        }
    }
    return res;
}

static format pp_name(name n) {
    return format(n.escape());
}

struct simple_pp_fn {
    type_checker m_tc;
    lowlevel_notations m_notations;
    unsigned m_indent = 0;

    simple_pp_fn(environment const & env, lowlevel_notations const & notations) :
            m_tc(env), m_notations(notations) {}

    static constexpr unsigned MAX_PRIO = 1024;
    struct result {
        format m_fmt;
        unsigned m_prio;

        result(format const & fmt, unsigned prio) : m_fmt(fmt), m_prio(prio) {}
        result(format const & fmt) : m_fmt(fmt), m_prio(MAX_PRIO) {}

        result maybe_paren() const { return maybe_paren(MAX_PRIO); }
        result maybe_paren(unsigned new_prio) const {
            if (m_prio < new_prio) {
                return paren(m_fmt);
            } else {
                return *this;
            }
        }

        operator format() const { return m_fmt; }
    };

    result pp_meta(name const & n) {
        return compose(format("?"), pp_name(n));
    }

    result pp_level(level const & l) {
        switch (l.kind()) {
            case level_kind::Zero: return format("0");
            case level_kind::Succ: return result(compose(pp_level(succ_of(l)).maybe_paren(1), format("+1")), 0);
            case level_kind::Max:
                return result(compose_many({format("max"), space(),
                                            pp_level(max_lhs(l)).maybe_paren(1),
                                            pp_level(max_rhs(l)).maybe_paren(1)}), 0);
            case level_kind::IMax:
                return result(compose_many({format("imax"), space(),
                                            pp_level(imax_lhs(l)).maybe_paren(1),
                                            pp_level(imax_rhs(l)).maybe_paren(1)}), 0);
            case level_kind::Param: return pp_name(param_id(l));
            case level_kind::Meta: return pp_meta(meta_id(l));
        }
        lean_unreachable();
    }

    result pp_var(expr const & e) {
        return compose(format("#"), format(var_idx(e)));
    }

    result pp_sort(expr const & e) {
        if (sort_level(e) == mk_level_zero()) {
            return format("Prop");
        } else if (sort_level(e) == mk_level_one()) {
            return format("Type");
        } else if (is_succ(sort_level(e))) {
            return compose_many({format("Type"), space(), pp_level(succ_of(sort_level(e))).maybe_paren()});
        } else {
            return compose_many({format("Sort"), space(), pp_level(sort_level(e)).maybe_paren()});
        }
    }

    result pp_const(expr const & e) {
        return pp_name(const_name(e));
    }

    result pp_meta(expr const & e) {
        return pp_meta(mlocal_name(e));
    }

    result pp_local(expr const & e) {
        return pp_name(mlocal_pp_name(e));
    }

    bool is_implicit(expr const & f) {
        if (!closed(f)) {
            // the Lean type checker assumes expressions are closed.
            return false;
        }
        try {
            expr t = m_tc.relaxed_whnf(m_tc.infer(f));
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

    expr get_explicit_args(expr e, buffer<expr> & args) {
        while (is_app(e)) {
            if (!is_implicit(app_fn(e))) {
                args.push_back(app_arg(e));
            }
            e = app_fn(e);
        }
        std::reverse(args.begin(), args.end());
        return e;
    }

    result pp_app(expr const & e) {
        buffer<expr> args;
        auto fn = get_explicit_args(e, args);

        if (is_constant(fn)) {
            auto it = m_notations.find(const_name(fn));
            if (it != m_notations.end()) {
                format fmt;
                auto prec = it->second.m_prec;
                if (it->second.m_kind == lowlevel_notation_kind::Postfix && args.size() == 1) {
                    fmt = compose_many({pp(args[0]).maybe_paren(prec), format(it->second.m_token)});
                }
                if (it->second.m_kind == lowlevel_notation_kind::Prefix && args.size() == 1) {
                    fmt = compose_many({format(it->second.m_token), pp(args[0]).maybe_paren(prec)});
                }
                if (it->second.m_kind == lowlevel_notation_kind::Infix && args.size() == 2) {
                    fmt = compose_many({pp(args[0]).maybe_paren(prec),
                                        format(it->second.m_token),
                                        pp(args[1]).maybe_paren(prec)});
                }
                if (!fmt.is_nil_fmt())
                    return result(group(fmt), it->second.m_prec-1);
            }
        }

        format fmt = pp(fn).maybe_paren();
        for (auto & arg : args) {
            fmt = compose_many({fmt, space(), pp(arg).maybe_paren()});
        }
        return result(group(fmt), MAX_PRIO-1);
    }

    std::unordered_set<name, name_hash> used_names;
    name get_unused(name n) {
        if (!used_names.count(n)) return n;

        n = n.get_subscript_base();
        for (unsigned i = 1;; i++) {
            auto n_i = n.append_after(i);
            if (!used_names.count(n_i))
                return n_i;
        }
    }

    struct local_const {
        simple_pp_fn * m_fn;
        name m_pp_name;
        expr m_lc;

        local_const(simple_pp_fn * fn, name pp_name, expr const & domain, binder_info const & bi) : m_fn(fn) {
            m_pp_name = m_fn->get_unused(pp_name);
            m_fn->used_names.insert(m_pp_name);
            m_lc = mk_local(m_pp_name, m_pp_name, domain, bi);
            m_fn->m_tc.push_local(m_pp_name, domain, bi);
        }
        ~local_const() {
            m_fn->used_names.erase(m_pp_name);
            m_fn->m_tc.pop_local();
        }

        expr const & domain() const { return mlocal_type(m_lc); }

        local_const(simple_pp_fn * fn, expr const & binder) :
                local_const(fn, binding_name(binder), binding_domain(binder), binding_info(binder)) {}
    };

    void mark_used_const_names(expr const & e) {
        for_each(e, [&] (expr const & c, unsigned) {
            if (is_constant(c))
                used_names.insert(const_name(c));
            return true;
        });
    }

    format wrap_binder(std::initializer_list<format> const & fmts, binder_info const & bi) {
        auto fmt = compose_many(fmts);
        if (bi.is_implicit()) {
            return compose_many({format("{"), fmt, format("}")});
        } else if (bi.is_strict_implicit()) {
            return compose_many({format("{{"), fmt, format("}}")});
        } else if (bi.is_inst_implicit()) {
            return compose_many({format("["), fmt, format("]")});
        } else {
            return fmt;
        }
    }

    result pp_lambda(expr const & e) {
        local_const lc(this, e);
        return result(group(compose_many({format("λ"), space(),
                                          wrap_binder({pp(lc.m_lc), space(), format(":"), space(),
                                                       pp(binding_domain(e)).maybe_paren(1)}, binding_info(e)),
                                          format(","), space(), pp(instantiate(binding_body(e), lc.m_lc))})), 0);
    }

    result pp_pi(expr e) {
        if (!has_free_vars(binding_body(e))) {
            // implication
            return result(group(compose_many({pp(binding_domain(e)).maybe_paren(25), space(), format("->"),
                                              space(), pp(binding_body(e)).maybe_paren(24)})), 24);
        } else {
            auto bi = binding_info(e);
            auto ty = binding_domain(e);

            buffer<local_const> lcs;
            do {
                lcs.emplace_back(this, e);
                e = instantiate(binding_body(e), lcs.back().m_lc);
            } while (is_pi(e) && has_free_vars(binding_body(e)) &&
                    binding_info(e) == bi &&
                    m_tc.is_def_eq(binding_domain(e), ty));

            format bound_vars;
            for (auto & lc : lcs) {
                if (!bound_vars.is_nil_fmt()) bound_vars = compose(bound_vars, space());
                bound_vars = compose_many({bound_vars, pp_name(lc.m_pp_name)});
            }

            auto fmt = compose_many({format("Π"), space(),
                                     wrap_binder({bound_vars, space(), format(":"), space(),
                                                  pp(ty).maybe_paren(1)}, bi),
                                     format(","), space(), pp(e)});
            return result(group(fmt), 0);
        }
    }

    result pp_macro(expr const &) {
        return format("[macro]");
    }

    result pp_let(expr const & e) {
        local_const lc(this, let_name(e), let_type(e), binder_info());
        return result(group(compose_many({format("let"), space(), pp(lc.m_lc), space(), format(":"), space(),
                                    pp(let_type(e)).maybe_paren(1), space(), format(":="), space(), pp(let_value(e)), format(","),
                                    space(), pp(instantiate(let_body(e), lc.m_lc))})), 0);
    }

    result pp(expr const & e) {
        switch (e.kind()) {
            case expr_kind::Var: return pp_var(e);
            case expr_kind::Sort: return pp_sort(e);
            case expr_kind::Constant: return pp_const(e);
            case expr_kind::Meta: return pp_meta(e);
            case expr_kind::Local: return pp_local(e);
            case expr_kind::App: return pp_app(e);
            case expr_kind::Lambda: return pp_lambda(e);
            case expr_kind::Pi: return pp_pi(e);
            case expr_kind::Macro: return pp_macro(e);
            case expr_kind::Let: return pp_let(e);
        }
        lean_unreachable();
    }
};

format simple_pp(name const & n) {
    return pp_name(n);
}

format simple_pp(environment const & env, expr const & e, lowlevel_notations const & notations) {
    simple_pp_fn fn(env, notations);
    fn.mark_used_const_names(e);
    return fn.pp(e);
}

}
