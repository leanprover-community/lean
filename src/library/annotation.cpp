/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include <memory>
#include <string>
#include "util/sstream.h"
#include "kernel/abstract_type_context.h"
#include "library/kernel_serializer.h"
#include "library/annotation.h"
#include "frontends/lean/json.h"

namespace lean {
static name * g_annotation = nullptr;
static std::string * g_annotation_opcode = nullptr;

name const & get_annotation_name() { return *g_annotation; }
std::string const & get_annotation_opcode() { return *g_annotation_opcode; }

/** \brief We use a macro to mark expressions that denote "let" and "have"-expressions.
    These marks have no real semantic meaning, but are useful for helping Lean's pretty printer.
*/
class annotation_macro_definition_cell : public macro_definition_cell {
    name m_name;
    void check_macro(expr const & m) const {
        if (!is_macro(m) || macro_num_args(m) != 1)
            throw exception(sstream() << "invalid '" << m_name << "' annotation, incorrect number of arguments");
    }
public:
    annotation_macro_definition_cell(name const & n):m_name(n) {}
    name const & get_annotation_kind() const { return m_name; }
    virtual name get_name() const override { return get_annotation_name(); }
    virtual void display(std::ostream & out) const override { out << m_name; }
    virtual expr check_type(expr const & m, abstract_type_context & ctx, bool infer_only) const override {
        check_macro(m);
        return ctx.check(macro_arg(m, 0), infer_only);
    }
    virtual optional<expr> expand(expr const & m, abstract_type_context &) const override {
        check_macro(m);
        return some_expr(macro_arg(m, 0));
    }
    virtual void write(serializer & s) const override {
        s.write_string(get_annotation_opcode());
        s << m_name;
    }
#ifdef LEAN_JSON
    virtual void write_json(abstract_ast_exporter &, json & j) const override {
        j["name"] = json_of_name(m_name);
    }
#endif
    virtual bool operator==(macro_definition_cell const & other) const override {
        if (auto other_ptr = dynamic_cast<annotation_macro_definition_cell const *>(&other)) {
            return m_name == other_ptr->m_name;
        } else {
            return false;
        }
    }
    virtual unsigned hash() const override {
        return ::lean::hash(m_name.hash(), g_annotation->hash());
    }
};

typedef std::unordered_map<name, macro_definition, name_hash, name_eq> annotation_macros;
static annotation_macros * g_annotation_macros = nullptr;

annotation_macros & get_annotation_macros() { return *g_annotation_macros; }

void register_annotation(name const & n) {
    annotation_macros & ms = get_annotation_macros();
    lean_assert(ms.find(n) == ms.end());
    ms.insert(mk_pair(n, macro_definition(new annotation_macro_definition_cell(n))));
}

expr mk_annotation(name const & kind, expr const & e, tag g) {
    annotation_macros & ms = get_annotation_macros();
    auto it = ms.find(kind);
    if (it != ms.end()) {
        return mk_macro(it->second, 1, &e, g);
    } else {
        throw exception(sstream() << "unknown annotation kind '" << kind << "'");
    }
}

expr mk_annotation(name const & kind, expr const & e) {
    return mk_annotation(kind, e, e.get_tag());
}

bool is_annotation(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == get_annotation_name();
}

name const & get_annotation_kind(expr const & e) {
    lean_assert(is_annotation(e));
    return static_cast<annotation_macro_definition_cell const*>(macro_def(e).raw())->get_annotation_kind();
}

bool is_annotation(expr const & e, name const & kind) {
    return is_annotation(e) && get_annotation_kind(e) == kind;
}

expr const & get_annotation_arg(expr const & e) {
    lean_assert(is_annotation(e));
    return macro_arg(e, 0);
}

bool is_nested_annotation(expr const & e, name const & kind) {
    expr const * it = &e;
    while (is_annotation(*it)) {
        if (get_annotation_kind(*it) == kind)
            return true;
        it = &get_annotation_arg(*it);
    }
    return false;
}

expr const & get_nested_annotation_arg(expr const & e) {
    expr const * it = &e;
    while (is_annotation(*it))
        it = &get_annotation_arg(*it);
    return *it;
}

expr copy_annotations(expr const & from, expr const & to) {
    buffer<expr> trace;
    expr const * it = &from;
    while (is_annotation(*it)) {
        trace.push_back(*it);
        it = &get_annotation_arg(*it);
    }
    expr r     = to;
    unsigned i = trace.size();
    while (i > 0) {
        --i;
        r = copy_tag(trace[i], mk_annotation(get_annotation_kind(trace[i]), r));
    }
    return r;
}

static name * g_have       = nullptr;
static name * g_show       = nullptr;
static name * g_suffices   = nullptr;
static name * g_checkpoint = nullptr;

expr mk_have_annotation(expr const & e) { return mk_annotation(*g_have, e); }
expr mk_show_annotation(expr const & e) { return mk_annotation(*g_show, e); }
expr mk_suffices_annotation(expr const & e) { return mk_annotation(*g_suffices, e); }
expr mk_checkpoint_annotation(expr const & e) { return mk_annotation(*g_checkpoint, e); }
bool is_have_annotation(expr const & e) { return is_annotation(e, *g_have); }
bool is_show_annotation(expr const & e) { return is_annotation(e, *g_show); }
bool is_suffices_annotation(expr const & e) { return is_annotation(e, *g_suffices); }
bool is_checkpoint_annotation(expr const & e) { return is_annotation(e, *g_checkpoint); }

void initialize_annotation() {
    g_annotation = new name("annotation");
    g_annotation_opcode = new std::string("Annot");
    g_annotation_macros = new annotation_macros();
    g_have       = new name("have");
    g_show       = new name("show");
    g_suffices   = new name("suffices");
    g_checkpoint = new name("checkpoint");

    register_annotation(*g_have);
    register_annotation(*g_show);
    register_annotation(*g_suffices);
    register_annotation(*g_checkpoint);

    register_macro_deserializer(get_annotation_opcode(),
                                [](deserializer & d, unsigned num, expr const * args) {
                                    if (num != 1)
                                        throw corrupted_stream_exception();
                                    name k;
                                    d >> k;
                                    return mk_annotation(k, args[0]);
                                });
}

void finalize_annotation() {
    delete g_checkpoint;
    delete g_show;
    delete g_have;
    delete g_suffices;
    delete g_annotation_macros;
    delete g_annotation_opcode;
    delete g_annotation;
}
}
