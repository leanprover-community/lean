/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
*/
#pragma once
#include <string>
#include "library/vm/vm.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_expr.h"
#include "util/sexpr/format.h"
#include "library/expr_address.h"
#include "frontends/lean/pp.h"
#include "kernel/environment.h"
#include "kernel/abstract_type_context.h"
#include "util/sexpr/options.h"
#include "util/sexpr/sexpr.h"
#include "library/pp_options.h"

namespace lean {
struct magic {
    vm_obj m_o;
    magic(vm_obj const & o) : m_o(o) {}
    magic(format const & f) : m_o(mk_vm_constructor(5, to_obj(f))) {}
    magic() : magic(format()) {}
    explicit magic(std::string const & v) : magic(format(v)) {}
    explicit magic(sexpr const & v) : magic(format(v)) {}
    explicit magic(unsigned i) : magic(format(i)) {}
    explicit magic(name const & n) : magic(format(n)) {}
    explicit magic(char const * v): magic(format(v)) {}
    friend magic operator+(magic const & f1, magic const & f2);
    magic & operator+=(magic const & f) {
        *this = *this + f;
        return *this;
    }
};

magic tag_expr(address const & a, expr const & e, magic const & m);
magic compose(magic const & f1, magic const & f2);
magic operator+(magic const & f1, magic const & f2);
magic group(magic const & f);
magic nest(int i, magic const & f);
magic highlight(magic const & f, format::format_color const c = format::RED);

magic bracket(std::string const & l, magic const & x, std::string const & r);
magic paren(magic const & x);
// magic above(magic const & f1, magic const & f2);
// magic wrap(magic const & f1, magic const & f2);
// magic highlight_keyword(magic const & f);
// magic highlight_builtin(magic const & f);
// magic highlight_command(magic const & f);

class magic_pretty_fn : public pretty_fn<magic> {
    magic of_rec(address const & a, expr const & e, magic const & result) {
        return tag_expr(a, e, result);
    }
public:
    magic_pretty_fn(environment const & e, options const & o, abstract_type_context & ctx) : pretty_fn<magic>(e, o, ctx) {}
};




vm_obj pp_magic(vm_obj const & vts, vm_obj const & ve);

void initialize_vm_pp();
void finalize_vm_pp();

}
