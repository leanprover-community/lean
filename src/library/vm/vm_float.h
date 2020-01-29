/* Copyright 2019 E.W.Ayers
Authors: E.W.Ayers, R.Y.Lewis */
#pragma once
#include <limits>
#include "library/vm/vm.h"

namespace lean{
vm_obj to_obj(float f);
float to_float(vm_obj const & o);
void initialize_vm_float();
void finalize_vm_float();
}
