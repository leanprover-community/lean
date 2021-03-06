/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/tactic/gexpr.h"

namespace lean {
expr gexpr::to_expr(type_context_old & ctx) const {
    if (m_univ_poly) {
        declaration const & fdecl = ctx.env().get(const_name(m_expr));
        buffer<level> ls_buffer;
        unsigned num_univ_ps = fdecl.get_num_univ_params();
        for (unsigned i = 0; i < num_univ_ps; i++)
            ls_buffer.push_back(ctx.mk_univ_metavar_decl());
        levels ls = to_list(ls_buffer.begin(), ls_buffer.end());
        return mk_constant(const_name(m_expr), ls);
    } else {
        return m_expr;
    }
}

bool operator==(gexpr const & ge1, gexpr const & ge2) { return ge1.m_expr == ge2.m_expr; }

std::ostream & operator<<(std::ostream & out, gexpr const & ge) {
    out << ge.m_expr;
    if (ge.is_universe_polymorphic()) out << " (poly)";
    return out;
}

io_state_stream const & operator<<(io_state_stream const & out, gexpr const & ge) {
    out << ge.m_expr;
    if (ge.is_universe_polymorphic()) out << " (poly)";
    return out;
}
}
