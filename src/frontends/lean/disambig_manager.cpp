/*
Copyright (c) Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Reid Barton
*/
#include "frontends/lean/disambig_manager.h"
#include "frontends/lean/parser.h"

namespace lean {

void disambig_manager::add_field(unsigned tag, name field) {
    unique_lock<mutex> lock(m_mutex);

    m_field_names.insert(tag, field);
}

void disambig_manager::add_local(unsigned tag, expr r) {
    unique_lock<mutex> lock(m_mutex);

    m_resolved_locals.insert(tag, r);
}

LEAN_THREAD_PTR(disambig_manager, g_disambig_m);
scoped_disambig_manager::scoped_disambig_manager(disambig_manager *dm) {
    m_old = g_disambig_m;
    g_disambig_m = dm;
}
scoped_disambig_manager::~scoped_disambig_manager() {
    g_disambig_m = m_old;
}
disambig_manager * get_global_disambig_manager() {
    return g_disambig_m;
}

}
