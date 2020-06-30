/*
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
*/
#include "library/expr_address.h"
namespace lean {

vm_obj to_obj(expr_coord c) {
    return mk_vm_simple(unsigned(c));
}
vm_obj to_obj(address c) {
    buffer<vm_obj> b;
    for_each(c, [&](expr_coord c) { b.push_back(to_obj(c)); });
    return to_obj(b);
}

namespace expr_address {

expr_coord to_coord(vm_obj const & c) {
    return static_cast<expr_coord>(cidx(c));
}
address to_address(vm_obj const & a) {
    list<expr_coord> adr = to_list<expr_coord>(a, [](vm_obj const & p) {
        return to_coord(p);
    });
    return adr;
}

address app(unsigned sz, unsigned i) {
    address result;
    if (sz <= i) {return result;}
    for (unsigned j = 0; j < sz - i - 1; j++) {
        result = cons(expr_coord::app_fn, result);
    }
    result = cons(expr_coord::app_arg, result);
    return result;
}

address fn(unsigned sz) {
    address result;
    for (unsigned i = 0; i < sz; i++) {
        result = cons(expr_coord::app_fn, result);
    }
    return result;
}

address arg() {
    return address(expr_coord::app_arg);
}

address pi_body(unsigned n) {
    address result;
    for (unsigned i = 0; i < n; i++) {
        result = cons(expr_coord::pi_body, result);
    }
    return result;
}

address binding_type(expr const & e) {
    lean_assert(is_binding(e));
    if (is_pi(e)) {
        return address(expr_coord::pi_var_type);
    } else {
        return address(expr_coord::lam_var_type);
    }
}
address binding_body(expr const & e) {
    lean_assert(is_binding(e));
    if (is_pi(e)) {
        return address(expr_coord::pi_body);
    } else {
        return address(expr_coord::lam_body);
    }
}
address lam_body(unsigned n) {
    address result;
    for (unsigned i = 0; i < n; i++) {
        result = cons(expr_coord::lam_body, result);
    }
    return result;
}

address repeat(address e, unsigned n) {
    address result;
    for (unsigned i = 0; i < n; i++) {
        result = append(e, result);
    }
    return result;
}

address mlocal_type(expr const & local) {
    lean_assert(is_mlocal(local));
    return is_local(local) ? address(expr_coord::local_const_type) : address(expr_coord::mvar_type);
}


}}
