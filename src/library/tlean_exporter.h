/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Daniel Selsam
*/
#pragma once

#include "kernel/expr_maps.h"
#include "kernel/inductive/inductive.h"
#include <unordered_map>
#include <unordered_set>

namespace lean {

template<typename T>
using level_map = typename std::unordered_map<level, T, level_hash, level_eq>;

template<typename T>
using name_hmap = typename std::unordered_map<name, T, name_hash, name_eq>;

class tlean_exporter {
 private:
    std::ostream &                      m_out;
    environment                         m_env;
    std::unordered_set<name, name_hash> m_exported;
    name_hmap<unsigned>                 m_name2idx;
    level_map<unsigned>                 m_level2idx;
    expr_bi_map<unsigned>               m_expr2idx;

    unsigned export_level(level const & l);
    void export_binder_info(binder_info const & bi);
    unsigned export_binding(expr const & e, char const * k);
    unsigned export_const(expr const & e);
    unsigned export_expr_core(expr const & e);

    void export_definition(declaration const & d);
    void export_axiom(declaration const & d);
    void export_declaration(name const & n);

public:
    tlean_exporter(std::ostream & out, environment const & env);
    unsigned export_name(name const & n);
    unsigned export_expr(expr const & e);
    void export_declaration(declaration const & d);
    void export_inductive(inductive::certified_inductive_decl const & d);

    std::ostream & out();
    environment & env();
};

}
