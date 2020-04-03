/*
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
*/
#pragma once
#include "kernel/environment.h"
#include "util/name.h"
namespace lean {
    bool get_vm_override_enabled(options const & opts);
    void initialize_vm_override();
    void finalize_vm_override();
}
