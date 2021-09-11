/*
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
*/
#include <string>
#include "util/optional.h"
#include "util/name.h"
#include "util/sexpr/option_declarations.h"
#include "library/attribute_manager.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm.h"
#include "frontends/lean/parser.h"

#define LEAN_DEFAULT_VM_OVERRIDE_ENABLED true

namespace lean {
static name * g_vm_override;
static name * g_vm_override_enabled;


struct vm_override_attribute_data : public attr_data {
    /** name of the override declaration. */
    name m_name;
    /** namespace */
    optional<name> m_ns;
    vm_override_attribute_data() {}
    vm_override_attribute_data(name const & n) : m_name(n) {}
    virtual unsigned hash() const override {return m_name.hash();}
    void write(serializer & s) const {s << m_name;}
    void read(deserializer & d) {
        m_name = read_name(d);
    }
    ast_id parse(abstract_parser & p) override {
        lean_assert(dynamic_cast<parser *>(&p));
        auto& p2 = *static_cast<parser *>(&p);
        auto n = p2.check_constant_next("not a constant");
        auto& data = p2.new_ast("vm_override", p2.pos());
        data.push(n.first);
        m_name = n.second;
        if (p2.curr_is_identifier()) {
            m_ns = optional<name>(p2.get_name_val());
            data.push(p2.new_ast("ident", p2.pos(), *m_ns).m_id);
            p2.next();
        } else {
            m_ns = optional<name>();
            data.push(0);
        }
        return data.m_id;
    }
};
bool operator==(vm_override_attribute_data const & d1, vm_override_attribute_data const & d2) {
    return d1.m_name == d2.m_name;
}

template class typed_attribute<vm_override_attribute_data>;
typedef typed_attribute<vm_override_attribute_data> vm_override_attribute;

static vm_override_attribute const & get_vm_override_attribute() {
    return static_cast<vm_override_attribute const &>(get_system_attribute(*g_vm_override));
}

bool get_vm_override_enabled(options const & opts) {
    return opts.get_bool(*g_vm_override_enabled, LEAN_DEFAULT_VM_OVERRIDE_ENABLED);
}

void initialize_vm_override() {
    g_vm_override = new name("vm_override");
    g_vm_override_enabled = new name("vm_override", "enabled");
    register_system_attribute(
      vm_override_attribute(*g_vm_override,
        "Override this declaration with the given declaration when evaluating in the VM.\n"
        "\n"
        "When overriding an inductive datatype, a second argument should be given containing"
        "the overrides for the constructors and recursors."
        ,
        [](environment const & env, io_state const &, name const & d, unsigned, bool) -> environment {
          // this is called when the attribute is added
          auto data = get_vm_override_attribute().get(env, d);
          return add_override(env, d, data->m_name, data->m_ns);
        } ) );
    register_bool_option(
        *g_vm_override_enabled,
        LEAN_DEFAULT_VM_OVERRIDE_ENABLED,
        "Enable/disable using VM overrides when compiling bytecode.");
}

void finalize_vm_override() {
}
}
