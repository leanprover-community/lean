/*
Copyright (c) E.W.Ayers 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
*/
#include "frontends/lean/json.h"
#include "library/vm/vm.h"

namespace lean {

json to_json(vm_obj const & o);
vm_obj to_obj(json const & j);

}
