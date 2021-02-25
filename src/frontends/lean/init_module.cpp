/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "frontends/lean/tokens.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/builtin_cmds.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/inductive_cmds.h"
#include "frontends/lean/structure_instance.h"
#include "frontends/lean/parse_table.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/match_expr.h"
#include "frontends/lean/notation_cmd.h"
#include "frontends/lean/tactic_notation.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/util.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/brackets.h"
#include "frontends/lean/interactive.h"
#include "frontends/lean/completion.h"
#include "frontends/lean/user_notation.h"
#include "frontends/lean/user_command.h"
#include "frontends/lean/widget.h"
#include "frontends/lean/eqn_api.h"

namespace lean {
void initialize_frontend_lean_module() {
    initialize_decl_attributes();
    initialize_prenum();
    initialize_tokens();
    initialize_token_table();
    initialize_parse_table();
    initialize_builtin_cmds();
    initialize_builtin_exprs();
    initialize_scanner();
    initialize_parser();
    initialize_parser_config();
    initialize_calc();
    initialize_inductive_cmds();
    initialize_structure_instance();
    initialize_pp();
    initialize_decl_cmds();
    initialize_match_expr();
    initialize_elaborator();
    initialize_notation_cmd();
    initialize_tactic_notation();
    initialize_frontend_lean_util();
    initialize_info_manager();
    initialize_brackets();
    initialize_interactive();
    initialize_completion();
    initialize_user_notation();
    initialize_user_command();
    initialize_widget();
    initialize_eqn_api();
}
void finalize_frontend_lean_module() {
    finalize_eqn_api();
    finalize_user_command();
    finalize_user_notation();
    finalize_completion();
    finalize_interactive();
    finalize_brackets();
    finalize_info_manager();
    finalize_frontend_lean_util();
    finalize_tactic_notation();
    finalize_notation_cmd();
    finalize_elaborator();
    finalize_match_expr();
    finalize_decl_cmds();
    finalize_pp();
    finalize_structure_instance();
    finalize_inductive_cmds();
    finalize_calc();
    finalize_parser_config();
    finalize_parser();
    finalize_scanner();
    finalize_builtin_exprs();
    finalize_builtin_cmds();
    finalize_parse_table();
    finalize_token_table();
    finalize_tokens();
    finalize_prenum();
    finalize_decl_attributes();
    finalize_widget();
}
}
