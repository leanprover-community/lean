/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/vm/vm.h"

namespace lean {
int to_int(vm_obj const & o);
optional<int> try_to_int(vm_obj const & o);
int force_to_int(vm_obj const & o, int def);

vm_obj mk_vm_int(int n);
vm_obj mk_vm_int(unsigned int n);
vm_obj mk_vm_int(long n);
vm_obj mk_vm_int(unsigned long n);
vm_obj mk_vm_int(long long n);
vm_obj mk_vm_int(unsigned long long n);
vm_obj mk_vm_int(double n);
vm_obj mk_vm_int(mpz const & n);

void initialize_vm_int();
void finalize_vm_int();
}
