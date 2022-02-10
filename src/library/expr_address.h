/*
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
*/
#pragma once
#include "util/list.h"
#include "kernel/expr.h"
#include "library/vm/vm.h"
#include "library/vm/vm_list.h"


namespace lean {
enum class expr_coord {
    app_fn, app_arg,
    lam_var_type, lam_body,
    pi_var_type, pi_body,
    elet_var_type , elet_assignment, elet_body,
};

typedef list<expr_coord> address;

vm_obj to_obj(expr_coord c);
vm_obj to_obj(address a);

namespace expr_address {
    expr_coord to_coord(vm_obj const & c);
    address to_address(vm_obj const & a);
    address app(unsigned sz = 1, unsigned i = 0);
    address fn(unsigned sz = 1);
    address arg();
    address pi_body(unsigned n = 1);
    address binding_body(expr const & binder);
    address binding_type(expr const & binder);
    address lam_body(unsigned n = 1);
    address repeat(address e, unsigned n);
}
}
