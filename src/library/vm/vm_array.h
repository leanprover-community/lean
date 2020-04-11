/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

#include "library/vm/vm.h"

namespace lean {

std::vector<vm_obj> const & to_array(vm_obj const & o);
vm_obj to_obj_array(std::vector<vm_obj> const & a);
vm_obj to_obj_array(std::vector<vm_obj> && a);

void initialize_vm_array();
void finalize_vm_array();
void initialize_vm_array_builtin_idxs();
}
