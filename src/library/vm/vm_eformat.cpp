/*
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
*/
#include <string>
#include "library/vm/vm_eformat.h"
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

eformat tag_expr(address const & a, expr const & e, eformat const & m) {
    if (is_nil(a)) { return m; }
    vm_obj tag = mk_vm_pair(to_obj(a), to_obj(e));
    return eformat(mk_vm_constructor(0, tag, m.m_o));
}
eformat compose(eformat const & f1, eformat const & f2) {
    return eformat(mk_vm_constructor(1, f1.m_o, f2.m_o));
}
eformat operator+(eformat const & f1, eformat const & f2) {
    return compose(f1, f2);
}
eformat group(eformat const & f) {
    return eformat(mk_vm_constructor(2, f.m_o));
}
eformat nest(int i, eformat const & f) {
    return eformat(mk_vm_constructor(3, to_obj(i), f.m_o));
}
eformat highlight(eformat const & f, format::format_color const c) {
    return eformat(mk_vm_constructor(4, mk_vm_simple(unsigned(c)), f.m_o));
}

// [NOTE] these are copied from format.cpp
eformat bracket(std::string const & l, eformat const & x, std::string const & r) {
    return group(nest(l.size(), eformat(l) + x + eformat(r)));
}
eformat paren(eformat const & x) {
    return group(nest(1, lp() + x + rp()));
}

vm_obj pp_eformat(vm_obj const & vts, vm_obj const & ve) {
    tactic_state ts = tactic::to_state(vts);
    expr e = to_expr(ve);
    options o = ts.get_options();
    if (get_pp_instantiate_mvars(o)) {
        e = metavar_context(ts.mctx()).instantiate_mvars(e);
    }
    type_context_old ctx = mk_cacheless_type_context_for(ts, transparency_mode::All);
    eformat_pretty_fn mpf = eformat_pretty_fn(ts.env(), o, ctx);
    eformat m = mpf(e);
    return m.m_o;
}

void initialize_vm_eformat() {
    DECLARE_VM_BUILTIN(name({"tactic_state", "pp_tagged"}), pp_eformat);
}
void finalize_vm_eformat() {}

}
