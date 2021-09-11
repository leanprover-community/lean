/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/parser.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/decl_util.h"
namespace lean {
environment definition_cmd_core(parser & p, decl_cmd_kind k, ast_id cmd_id, cmd_meta const & meta);

environment single_definition_cmd_core(parser_info & p, decl_cmd_kind kind, ast_data * parent, cmd_meta meta);

environment ensure_decl_namespaces(environment const & env, name const & full_n);
}
