/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/find_fn.h"
#include "library/locals.h"
#include "frontends/lean/local_context_adapter.h"

namespace lean {
bool local_context_adapter::has_local_ref(expr const & e) {
    return static_cast<bool>(find(e, [](expr const & e, unsigned) { return is_local_decl_ref(e); }));
}

bool local_context_adapter::has_regular_local(expr const & e) {
    return static_cast<bool>(find(e, [](expr const & e, unsigned) { return is_local(e) && !is_local_decl_ref(e); }));
}

void local_context_adapter::add_local(expr const & local) {
    expr const & local_type = mlocal_type(local);
    expr new_local_type = translate_to(local_type);
    expr new_local_ref  = m_lctx.mk_local_decl(mlocal_pp_name(local), new_local_type, local_info(local));
    m_locals.push_back(local);
    m_local_refs.push_back(new_local_ref);
}

local_context_adapter::local_context_adapter(local_expr_decls const & ldecls) {
    lean_assert(m_lctx.empty() && m_locals.empty());
    buffer<pair<name, expr>> entries;
    to_buffer(ldecls.get_entries(), entries);
    unsigned i = entries.size();
    while (i > 0) {
        --i;
        pair<name, expr> const & entry = entries[i];
        expr const & local = entry.second;
        if (!is_local(local)) continue;
        add_local(local);
    }
}

local_context_adapter::local_context_adapter(list<expr> const & lctx) {
    lean_assert(std::all_of(lctx.begin(), lctx.end(), is_local));
    lean_assert(m_lctx.empty() && m_locals.empty());
    buffer<expr> entries;
    to_buffer(lctx, entries);
    unsigned i = entries.size();
    while (i > 0) {
        --i;
        add_local(entries[i]);
    }
}

expr local_context_adapter::translate_to(expr const & e) const {
    lean_assert(!has_local_ref(e));
    expr r = replace_locals(e, m_locals, m_local_refs);
    // lean_assert(!has_regular_local(r));
    return r;
}

expr local_context_adapter::translate_from(expr const & e) const {
    // lean_assert(!has_regular_local(e));
    expr r = replace_locals(e, m_local_refs, m_locals);
    lean_assert(!has_local_ref(r));
    return r;
}
}
