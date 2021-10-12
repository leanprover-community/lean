/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include "library/vm/vm.h"
#include "frontends/lean/parser.h"

namespace lean {
pair<ast_id, vm_obj> run_parser(parser & p, expr const & spec, buffer<vm_obj> const & args = {}, bool allow_profiler = false);
expr parse_interactive_param(parser & p, ast_data & parent, expr const & param_ty);

vm_obj to_obj(cmd_meta const & meta);

void initialize_vm_parser();
void finalize_vm_parser();
}

