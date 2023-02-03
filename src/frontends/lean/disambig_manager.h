/*
Copyright (c) Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Reid Barton
*/
#pragma once
#include "kernel/expr.h"
#include "util/rb_map.h"

namespace lean {
class parser;

class disambig_manager {
    mutable mutex m_mutex;
    /** Map: tag of a field_notation expr -> full name of the field */
    rb_map<unsigned, name, unsigned_cmp> m_field_names;
    rb_map<unsigned, expr, unsigned_cmp> m_resolved_locals;

public:
    void add_field(unsigned tag, name field);
    void add_local(unsigned tag, expr r);
    disambig_manager() {}
    rb_map<unsigned, name, unsigned_cmp> const & get_field_names() const { return m_field_names; };
    rb_map<unsigned, expr, unsigned_cmp> const & get_resolved_locals() const { return m_resolved_locals; };
};

disambig_manager * get_global_disambig_manager();
class scoped_disambig_manager {
    disambig_manager * m_old;
public:
    scoped_disambig_manager(disambig_manager * dm);
    ~scoped_disambig_manager();
    disambig_manager * get() { return m_old; }
};

}
