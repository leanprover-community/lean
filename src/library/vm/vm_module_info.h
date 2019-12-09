/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include "library/vm/vm.h"
#include "library/module_mgr.h"

namespace lean {
std::shared_ptr<module_info const> const & to_module_info(vm_obj const & o);
vm_obj to_obj(std::shared_ptr<module_info const> const & mi);
void initialize_vm_module_info();
void finalize_vm_module_info();
}
