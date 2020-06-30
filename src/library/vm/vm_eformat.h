/*
Copyright (c) E.W.Ayers. All rights reserved.
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
/** tagged_format (expr.address * expr) */
struct eformat {
    vm_obj m_o;
    eformat(vm_obj const & o) : m_o(o) {}
    eformat(format const & f) : m_o(mk_vm_constructor(5, to_obj(f))) {}
    eformat() : eformat(format()) {}
    explicit eformat(std::string const & v) : eformat(format(v)) {}
    explicit eformat(sexpr const & v) : eformat(format(v)) {}
    explicit eformat(unsigned i) : eformat(format(i)) {}
    explicit eformat(name const & n) : eformat(format(n)) {}
    explicit eformat(char const * v): eformat(format(v)) {}
    friend eformat operator+(eformat const & f1, eformat const & f2);
    eformat & operator+=(eformat const & f) {
        *this = *this + f;
        return *this;
    }
};

eformat tag_expr(address const & a, expr const & e, eformat const & m);
eformat compose(eformat const & f1, eformat const & f2);
eformat operator+(eformat const & f1, eformat const & f2);
eformat group(eformat const & f);
eformat nest(int i, eformat const & f);
eformat highlight(eformat const & f, format::format_color const c = format::RED);

eformat bracket(std::string const & l, eformat const & x, std::string const & r);
eformat paren(eformat const & x);

class eformat_pretty_fn : public pretty_fn<eformat> {
    eformat tag(address const & a, expr const & e, eformat const & result) {
        return tag_expr(reverse(a), e, result);
    }
public:
    eformat_pretty_fn(environment const & e, options const & o, abstract_type_context & ctx) : pretty_fn<eformat>(e, o, ctx) {}
};

vm_obj pp_eformat(vm_obj const & vts, vm_obj const & ve);

void initialize_vm_eformat();
void finalize_vm_eformat();

}
