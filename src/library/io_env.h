/*
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Simon Hudon
*/

#include <string>
#include "kernel/environment.h"

namespace lean {
environment set_cwd(environment const & env, std::string cwd);
std::string get_cwd(environment const & env);
void initialize_io_env();
void finalize_io_env();
}
