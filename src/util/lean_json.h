/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Mario Carneiro
*/
#pragma once
#ifdef LEAN_JSON
#include "util/json.hpp"

namespace lean {
using json = nlohmann::json;
}

#else

namespace lean {
struct json;
}
#endif
