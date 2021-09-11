/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "kernel/error_msgs.h"
#include "kernel/kernel_exception.h"
#include "kernel/abstract_type_context.h"
#include "library/util.h"
#include "library/kernel_serializer.h"

namespace lean {
static name * g_typed_expr_name = nullptr;
static std::string * g_typed_expr_opcode = nullptr;
static macro_definition * g_typed_expr = nullptr;

name const & get_typed_expr_name() { return *g_typed_expr_name; }
std::string const & get_typed_expr_opcode() { return *g_typed_expr_opcode; }

/** \brief This macro is used to "enforce" a given type to an expression.
    It is equivalent to

        definition typed_expr (A : Type) (a : A) := a

    We use a macro instead of the definition because we want to be able
    to use in any environment, even one that does not contain the
    definition such as typed_expr.

    The macro is also slightly for efficient because we don't need a
    universe parameter.
*/
class typed_expr_macro_definition_cell : public macro_definition_cell {
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 2)
            throw exception("invalid typed-expr, incorrect number of arguments");
    }
public:
    virtual name get_name() const { return get_typed_expr_name(); }
    virtual expr check_type(expr const & m, abstract_type_context & ctx, bool infer_only) const {
        check_macro(m);
        expr given_type = macro_arg(m, 0);
        if (!infer_only) {
            ctx.check(given_type, infer_only);
            expr inferred_type = ctx.check(macro_arg(m, 1), infer_only);
            if (!ctx.is_def_eq(inferred_type, given_type)) {
                throw_kernel_exception(ctx.env(), m, [=](formatter const & fmt) {
                    return format("type mismatch at term") + pp_type_mismatch(fmt, macro_arg(m, 1), inferred_type, given_type);
                });
            }
        }
        return given_type;
    }
    virtual optional<expr> expand(expr const & m, abstract_type_context &) const {
        check_macro(m);
        return some_expr(macro_arg(m, 1));
    }
    virtual void write(serializer & s) const {
        s.write_string(get_typed_expr_opcode());
    }
#ifdef LEAN_JSON
    virtual void write_json(abstract_ast_exporter &, json &) const override {}
#endif
};

bool is_typed_expr(expr const & e) {
    return is_macro(e) && macro_def(e) == *g_typed_expr;
}

expr mk_typed_expr(expr const & t, expr const & v, tag g = nulltag) {
    expr args[2] = {t, v};
    return mk_macro(*g_typed_expr, 2, args, g);
}

expr get_typed_expr_type(expr const & e) { lean_assert(is_typed_expr(e)); return macro_arg(e, 0); }
expr get_typed_expr_expr(expr const & e) { lean_assert(is_typed_expr(e)); return macro_arg(e, 1); }

void initialize_typed_expr() {
    g_typed_expr_name = new name("typed_expr");
    g_typed_expr_opcode = new std::string("TyE");
    g_typed_expr = new macro_definition(new typed_expr_macro_definition_cell());
    register_macro_deserializer(*g_typed_expr_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    if (num != 2)
                                        throw corrupted_stream_exception();
                                    return mk_typed_expr(args[0], args[1]);
                                });
}

void finalize_typed_expr() {
    delete g_typed_expr;
    delete g_typed_expr_opcode;
    delete g_typed_expr_name;
}
}
