/*
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
*/
#include <string>
#include "util/optional.h"
#include "util/name.h"
#include "library/attribute_manager.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm.h"
#include "frontends/lean/parser.h"

namespace lean {
static name * g_vm_override;
struct vm_override_attribute_data : public attr_data {
    name m_name;
    optional<name> m_ns;
    vm_override_attribute_data() {}
    vm_override_attribute_data(name const & n) : m_name(n) {}
    virtual unsigned hash() const override {return m_name.hash();}
    void write(serializer & s) const {s << m_name;}
    void read(deserializer & d) {
        m_name = read_name(d);
    }
    void parse(abstract_parser & p) override {
        lean_assert(dynamic_cast<parser *>(&p));
        auto & p2 = *static_cast<parser *>(&p);
        auto n = p2.check_constant_next("not a constant");
        m_name = n;
        if (p2.curr_is_identifier()) {
            m_ns = optional<name>(p2.get_name_val());
            p2.next();
        } else {
            m_ns = optional<name>();
        }
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

void initialize_vm_override() {
    g_vm_override = new name("vm_override");
    register_system_attribute(
      vm_override_attribute(*g_vm_override, "Override this declaration with the given declaration when evaluating in the VM."
        , [](environment const & env, io_state const &, name const & d, unsigned, bool) -> environment {
          // this is called when the attribute is added
          auto data = get_vm_override_attribute().get(env, d);
          return add_override(env, d, data->m_name, data->m_ns);
        } ) );
}

void finalize_vm_override() {}
}
