/*
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Simon Hudon
*/
#pragma once
#include "kernel/environment.h"

namespace lean {

void initialize_eqn_api();
void finalize_eqn_api();
environment store_eqn_spec(environment const & env, name const & n, expr const & e);
optional<expr> get_eqn_spec(environment const & env, name const & n);

}
