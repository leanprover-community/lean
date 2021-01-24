/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Daniel Selsam
*/
#include <iostream>
#include "library/tlean_exporter.h"
#include "library/unfold_macros.h"
#include "kernel/quotient/quotient.h"
#include "kernel/for_each_fn.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/module.h"
#include "library/class.h"
#include "library/attribute_manager.h"

namespace lean {

unsigned tlean_exporter::export_name(name const & n) {
    auto it = m_name2idx.find(n);
    if (it != m_name2idx.end()) {
        return it->second;
    }

    unsigned i;
    if (n.is_anonymous()) {
        lean_unreachable();
    } else if (n.is_string()) {
        unsigned p = export_name(n.get_prefix());
        i = static_cast<unsigned>(m_name2idx.size());
        m_out << i << " #NS " << p << " " << n.get_string() << std::endl;
    } else {
        unsigned p = export_name(n.get_prefix());
        i = static_cast<unsigned>(m_name2idx.size());
        m_out << i << " #NI " << p << " " << n.get_numeral() << std::endl;
    }
    m_name2idx[n] = i;
    return i;
}

unsigned tlean_exporter::export_level(level const & l) {
    auto it = m_level2idx.find(l);
    if (it != m_level2idx.end())
        return it->second;
    unsigned i = 0;
    unsigned l1, l2, n;
    switch (l.kind()) {
    case level_kind::Zero:
        lean_unreachable();
        break;
    case level_kind::Succ:
        l1 = export_level(succ_of(l));
        i = static_cast<unsigned>(m_level2idx.size());
        m_out << i << " #US " << l1 << std::endl;
        break;
    case level_kind::Max:
        l1 = export_level(max_lhs(l));
        l2 = export_level(max_rhs(l));
        i = static_cast<unsigned>(m_level2idx.size());
        m_out << i << " #UM " << l1 << " " << l2 << std::endl;
        break;
    case level_kind::IMax:
        l1 = export_level(imax_lhs(l));
        l2 = export_level(imax_rhs(l));
        i = static_cast<unsigned>(m_level2idx.size());
        m_out << i << " #UIM " << l1 << " " << l2 << std::endl;
        break;
    case level_kind::Param:
        n = export_name(param_id(l));
        i = static_cast<unsigned>(m_level2idx.size());
        m_out << i << " #UP " << n << std::endl;
        break;
    case level_kind::Meta:
        throw exception("invalid 'export', universe meta-variables cannot be exported");
    }
    m_level2idx[l] = i;
    return i;
}

void tlean_exporter::export_binder_info(binder_info const & bi) {
    if (bi.is_implicit())
        m_out << "#BI";
    else if (bi.is_strict_implicit())
        m_out << "#BS";
    else if (bi.is_inst_implicit())
        m_out << "#BC";
    else
        m_out << "#BD";
}

unsigned tlean_exporter::export_binding(expr const & e, char const * k) {
    unsigned n  = export_name(binding_name(e));
    unsigned e1 = export_expr_core(binding_domain(e));
    unsigned e2 = export_expr_core(binding_body(e));
    unsigned i = static_cast<unsigned>(m_expr2idx.size());
    m_out << i << " " << k << " ";
    export_binder_info(binding_info(e));
    m_out << " " << n << " " << e1 << " " << e2 << std::endl;
    return i;
}

unsigned tlean_exporter::export_const(expr const & e) {
    buffer<unsigned> ls;
    unsigned n = export_name(const_name(e));
    for (level const & l : const_levels(e))
        ls.push_back(export_level(l));
    unsigned i = static_cast<unsigned>(m_expr2idx.size());
    m_out << i << " #EC " << n;
    for (unsigned l : ls)
        m_out << " " << l;
    m_out << std::endl;
    return i;
}

unsigned tlean_exporter::export_expr_core(expr const & e) {
    auto it = m_expr2idx.find(e);
    if (it != m_expr2idx.end())
        return it->second;
    unsigned i = 0;
    unsigned l, e1, e2;
    switch (e.kind()) {
    case expr_kind::Var:
        i = static_cast<unsigned>(m_expr2idx.size());
        m_out << i << " #EV " << var_idx(e) << std::endl;
        break;
    case expr_kind::Sort:
        l = export_level(sort_level(e));
        i = static_cast<unsigned>(m_expr2idx.size());
        m_out << i << " #ES " << l << std::endl;
        break;
    case expr_kind::Constant:
        i = export_const(e);
        break;
    case expr_kind::App:
        e1 = export_expr_core(app_fn(e));
        e2 = export_expr_core(app_arg(e));
        i = static_cast<unsigned>(m_expr2idx.size());
        m_out << i << " #EA " << e1 << " " << e2 << std::endl;
        break;
    case expr_kind::Let: {
        auto n = export_name(let_name(e));
        e1 = export_expr_core(let_type(e));
        e2 = export_expr_core(let_value(e));
        auto e3 = export_expr_core(let_body(e));
        i = static_cast<unsigned>(m_expr2idx.size());
        m_out << i << " #EZ " << n << " " << e1 << " " << e2 << " " << e3 << std::endl;
        break;
    }
    case expr_kind::Lambda:
        i = export_binding(e, "#EL");
        break;
    case expr_kind::Pi:
        i = export_binding(e, "#EP");
        break;
    case expr_kind::Meta:
        throw exception("invalid 'export', meta-variables cannot be exported");
    case expr_kind::Local:
        throw exception("invalid 'export', local constants cannot be exported");
    case expr_kind::Macro:
        throw exception("invalid 'export', macros cannot be exported");
    }
    m_expr2idx[e] = i;
    return i;
}

unsigned tlean_exporter::export_expr(expr const & e) {
    return export_expr_core(unfold_all_macros(m_env, e));
}

void tlean_exporter::export_definition(declaration const & d) {
    auto hints = d.get_hints();
    unsigned n = export_name(d.get_name());
    auto ps = map2<unsigned>(d.get_univ_params(), [&] (name const & p) { return export_name(p); });
    auto t = export_expr(d.get_type());
    auto v = export_expr(d.get_value());

    m_out << "#DEF " << n << " " << d.is_theorem() << " ";
    if (hints.get_kind() == reducibility_hints::kind::Abbreviation) {
        m_out << "A ";
    } else if (hints.get_kind() == reducibility_hints::kind::Opaque) {
        m_out << "O ";
    } else {
        m_out << hints.get_height() << " ";
    }

    m_out << t << " " << v;
    for (unsigned p : ps)
        m_out << " " << p;
    m_out << std::endl;
}

void tlean_exporter::export_axiom(declaration const & d) {
    unsigned n = export_name(d.get_name());
    auto ps = map2<unsigned>(d.get_univ_params(), [&] (name const & p) { return export_name(p); });
    auto t = export_expr(d.get_type());
    m_out << "#AX " << n << " " << t;
    for (unsigned p : ps)
        m_out << " " << p;
    m_out << std::endl;
}

void tlean_exporter::export_declaration(declaration const & d) {
    if (!d.is_trusted()) return;

    if (d.is_definition()) {
        export_definition(d);
    } else {
        export_axiom(d);
    }
}

void tlean_exporter::export_inductive(inductive::certified_inductive_decl const & cdecl) {
    if (!cdecl.is_trusted()) return;
    inductive::inductive_decl decl = cdecl.get_decl();
    for (auto & p : decl.m_level_params)
        export_name(p);

    export_name(decl.m_name);
    export_expr(decl.m_type);

    for (auto & c : decl.m_intro_rules) {
        export_name(inductive::intro_rule_name(c));
        export_expr(inductive::intro_rule_type(c));
    }

    m_out << "#IND " << decl.m_num_params << " "
          << export_name(decl.m_name) << " "
          << export_expr(decl.m_type) << " "
          << length(decl.m_intro_rules);
    for (auto & c : decl.m_intro_rules) {
        // intro rules are stored as local constants, we split them up so that
        // the type checkers do not need to implement local constants.
        m_out << " " << export_name(inductive::intro_rule_name(c))
              << " " << export_expr(inductive::intro_rule_type(c));
    }
    for (name const & p : decl.m_level_params)
        m_out << " " << export_name(p);

    m_out << std::endl;
}

tlean_exporter::tlean_exporter(std::ostream & out, environment const & env) : m_out(out), m_env(env) {
    m_name2idx[{}]  = 0;
    m_level2idx[{}] = 0;
}

std::ostream & tlean_exporter::out() {
    return m_out;
}

environment & tlean_exporter::env() {
    return m_env;
}

}
