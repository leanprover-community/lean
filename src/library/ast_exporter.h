/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Mario Carneiro
*/
#pragma once

#include "frontends/lean/parser.h"

namespace lean {

class abstract_ast_exporter {
public:
    virtual unsigned export_level(const level & l) = 0;
    virtual unsigned export_expr(const expr & l) = 0;
};

void export_ast(parser &);

}
