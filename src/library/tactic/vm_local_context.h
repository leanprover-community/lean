/* Copyright 2019 E.W.Ayers */
#pragma once
#include "library/local_context.h"
#include "library/vm/vm.h"
namespace lean {
    local_context to_local_context(vm_obj const & o);
    vm_obj to_obj(local_context const & lc);
    void initialize_vm_local_context();
    void finalize_vm_local_context();
}
