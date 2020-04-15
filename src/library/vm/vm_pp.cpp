/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
*/
#include <string>
#include "library/vm/vm_pp.h"
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
#include "library/tactic/tactic_state.h"
#include "library/type_context.h"

namespace lean {

magic tag_expr(address const & a, expr const & e, magic const & m) {
    if (is_nil(a)) { return m; }
    return magic(mk_vm_constructor(0, to_obj(a), to_obj(e), m.m_o));
}
magic compose(magic const & f1, magic const & f2) {
    return magic(mk_vm_constructor(1, f1.m_o, f2.m_o));
}
magic operator+(magic const & f1, magic const & f2) {
    return compose(f1, f2);
}
magic group(magic const & f) {
    return magic(mk_vm_constructor(2, f.m_o));
}
magic nest(int i, magic const & f) {
    return magic(mk_vm_constructor(3, to_obj(i), f.m_o));
}
magic highlight(magic const & f, format::format_color const c) {
    return magic(mk_vm_constructor(4, mk_vm_simple(unsigned(c)), f.m_o));
}

// [fixme] these are copied from format.cpp
magic bracket(std::string const & l, magic const & x, std::string const & r) {
    return group(nest(l.size(), magic(l) + x + magic(r)));
}
magic paren(magic const & x) {
    return group(nest(1, lp() + x + rp()));
}

vm_obj pp_magic(vm_obj const & vts, vm_obj const & ve) {
    tactic_state ts = tactic::to_state(vts);
    expr e = to_expr(ve);
    options o = ts.get_options();
    if (get_pp_instantiate_mvars(o)) {
        e = metavar_context(ts.mctx()).instantiate_mvars(e);
    }
    type_context_old ctx = mk_cacheless_type_context_for(ts, transparency_mode::All);
    magic_pretty_fn mpf = magic_pretty_fn(ts.env(), o, ctx);
    magic m = mpf(e);
    return m.m_o;
}

void initialize_vm_pp() {
    DECLARE_VM_BUILTIN(name({"tactic_state", "pp_magic"}), pp_magic);
}
void finalize_vm_pp() {}

}
