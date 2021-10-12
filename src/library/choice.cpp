/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/for_each_fn.h"
#include "library/choice.h"
#include "library/kernel_serializer.h"

namespace lean {
static name * g_choice_name = nullptr;
static std::string * g_choice_opcode = nullptr;

[[ noreturn ]] static void throw_ex() { throw exception("unexpected occurrence of 'choice' expression"); }

// We encode a 'choice' expression using a macro.
// This is a trick to avoid creating a new kind of expression.
// 'Choice' expressions are temporary objects used by the elaborator,
// and have no semantic significance.
class choice_macro_cell : public macro_definition_cell {
public:
    virtual name get_name() const override { return *g_choice_name; }
    // Choice expressions must be replaced with metavariables before invoking the type checker.
    // Choice expressions cannot be exported. They are transient/auxiliary objects.
    virtual expr check_type(expr const &, abstract_type_context &, bool) const override { throw_ex(); }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const override { throw_ex(); }
    virtual void write(serializer & s) const override {
        // we should be able to write choice expressions because of notation declarations
        s.write_string(*g_choice_opcode);
    }
#ifdef LEAN_JSON
    virtual void write_json(abstract_ast_exporter &, json &) const override {}
#endif
};

static macro_definition * g_choice = nullptr;
expr mk_choice(unsigned num_es, expr const * es) {
    lean_assert(num_es > 0);
    if (num_es == 1)
        return es[0];
    else
        return mk_macro(*g_choice, num_es, es);
}

list<list<name>> collect_choice_symbols(expr const & e) {
    buffer<list<name>> r;
    for_each(e, [&](expr const & e, unsigned) {
            if (is_choice(e)) {
                buffer<name> cs;
                for (unsigned i = 0; i < get_num_choices(e); i++) {
                    expr const & c = get_app_fn(get_choice(e, i));
                    if (is_constant(c))
                        cs.push_back(const_name(c));
                    else if (is_local(c))
                        cs.push_back(mlocal_pp_name(c));
                }
                if (cs.size() > 1)
                    r.push_back(to_list(cs));
            }
            return true;
        });
    return to_list(r);
}

format pp_choice_symbols(expr const & e) {
    list<list<name>> symbols = collect_choice_symbols(e);
    if (symbols) {
        format r;
        bool first = true;
        for (auto cs : symbols) {
            format aux("overloads:");
            for (auto s : cs)
                aux += space() + format(s);
            if (!first)
                r += line();
            r += aux;
            first = false;
        }
        return r;
    } else {
        return format();
    }
}

void initialize_choice() {
    g_choice_name   = new name("choice");
    g_choice_opcode = new std::string("Choice");
    g_choice        = new macro_definition(new choice_macro_cell());
    register_macro_deserializer(*g_choice_opcode,
                                [](deserializer &, unsigned num, expr const * args) {
                                    return mk_choice(num, args);
                                });
}

void finalize_choice() {
    delete g_choice;
    delete g_choice_opcode;
    delete g_choice_name;
}

bool is_choice(expr const & e) {
    return is_macro(e) && macro_def(e) == *g_choice;
}

unsigned get_num_choices(expr const & e) {
    lean_assert(is_choice(e));
    return macro_num_args(e);
}

expr const & get_choice(expr const & e, unsigned i) {
    lean_assert(is_choice(e));
    return macro_arg(e, i);
}
}
