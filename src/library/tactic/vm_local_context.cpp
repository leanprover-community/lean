/* Copyright 2019 E.W.Ayers */
#include "library/local_context.h"
#include "library/vm/vm.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_option.h"
namespace lean {
struct vm_local_context : public vm_external {
    local_context m_val;
    vm_local_context(local_context const & v): m_val(v) {}
    virtual ~vm_local_context() {}
    virtual void dealloc() override { this->~vm_local_context(); get_vm_allocator().deallocate(sizeof(vm_local_context), this);}
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_local_context(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_local_context))) vm_local_context(m_val); }
    virtual unsigned int hash() { return 0; }
};
vm_obj to_obj(local_context const & lc) {
    return mk_vm_external(new(get_vm_allocator().allocate(sizeof(vm_local_context))) vm_local_context(lc));
}
local_context to_local_context(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_local_context*>(to_external(o)));
    return static_cast<vm_local_context*>(to_external(o))->m_val;
}

vm_obj to_obj(local_decl const & ld) {
    vm_obj args[6] = {
        to_obj(ld.get_name()),
        to_obj(ld.get_pp_name()),
        to_obj(ld.get_type()),
        to_obj(ld.get_value()),
        to_obj(ld.get_info()),
        to_obj(ld.get_idx())
    };
    return mk_vm_constructor(0, 6, args);
}

vm_obj lc_mk_empty() {
    local_context lc;
    return to_obj(lc);
}

vm_obj lc_mk_local_decl(vm_obj const & pn, vm_obj const & y, vm_obj const & bi, vm_obj const & lc) {
    local_context lctx = to_local_context(lc);
    expr h = lctx.mk_local_decl(to_name(pn), to_expr(y), to_binder_info(bi));
    return mk_vm_some(mk_vm_pair(to_obj(h), to_obj(lctx)));
}
vm_obj lc_get_local(vm_obj const & n, vm_obj const & lc) {
    optional<local_decl> o = to_local_context(lc).find_local_decl(to_name(n));
    if (o) {  return mk_vm_some(to_obj(o->mk_ref()));
    } else {  return mk_vm_none();
    }
}

vm_obj lc_get_local_decl(vm_obj const & n, vm_obj const & lc) {
    optional<local_decl> o = to_local_context(lc).find_local_decl(to_name(n));
    return to_obj(o);
}

vm_obj lc_is_subset(vm_obj const & lc1, vm_obj const & lc2) {
    return mk_vm_bool(
        to_local_context(lc1)
        .is_subset_of(to_local_context(lc2)));
}

vm_obj lc_has_decidable_eq(vm_obj const & lc1, vm_obj const & lc2) {
    return mk_vm_bool(equal_locals(to_local_context(lc1), to_local_context(lc2)));
}

vm_obj lc_fold(vm_obj const &, vm_obj const & f0, vm_obj const & a0, vm_obj const & lc0) {
    vm_obj r0 = a0;
    to_local_context(lc0).for_each([&](local_decl const & ld) {
        r0 = invoke(f0, r0, to_obj(ld.mk_ref()));
    });
    return r0;
}

void initialize_vm_local_context() {
    DECLARE_VM_BUILTIN(name({"local_context", "empty"}),  lc_mk_empty);
    DECLARE_VM_BUILTIN(name({"local_context", "mk_local"}),  lc_mk_local_decl);
    DECLARE_VM_BUILTIN(name({"local_context", "get_local"}), lc_get_local);
    DECLARE_VM_BUILTIN(name({"local_context", "get_local_decl"}), lc_get_local_decl);
    DECLARE_VM_BUILTIN(name({"local_context", "is_subset"}), lc_is_subset);
    DECLARE_VM_BUILTIN(name({"local_context", "has_decidable_eq"}), lc_has_decidable_eq);
    DECLARE_VM_BUILTIN(name({"local_context", "fold"}), lc_fold);
}
void finalize_vm_local_context() {
}
}
