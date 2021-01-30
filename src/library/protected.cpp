/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include "util/name_set.h"
#include "library/protected.h"
#include "library/module.h"

namespace lean {
struct protected_ext : public environment_extension {
    name_set m_protected; // protected declarations
};

struct protected_ext_reg {
    unsigned m_ext_id;
    protected_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<protected_ext>()); }
};

static protected_ext_reg * g_ext = nullptr;
static protected_ext const & get_extension(environment const & env) {
    return static_cast<protected_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, protected_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<protected_ext>(ext));
}

struct protected_modification : public modification {
    LEAN_MODIFICATION("prt")

    name m_name;

    protected_modification() {}
    protected_modification(name const & n) : m_name(n) {}

    void perform(environment & env) const override {
        protected_ext ext = get_extension(env);
        ext.m_protected.insert(m_name);
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_name;
    }

    void textualize(tlean_exporter & x) const override {
        unsigned n = x.export_name(m_name);
        x.out() << "#PROTECTED " << n << std::endl;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<protected_modification>(read_name(d));
    }
};

environment add_protected(environment const & env, name const & n) {
    return module::add_and_perform(env, std::make_shared<protected_modification>(n));
}

bool is_protected(environment const & env, name const & n) {
    return get_extension(env).m_protected.contains(n);
}

name get_protected_shortest_name(name const & n) {
    if (n.is_atomic() || n.get_prefix().is_atomic()) {
        return n;
    } else {
        name new_prefix = n.get_prefix().replace_prefix(n.get_prefix().get_prefix(), name());
        return n.replace_prefix(n.get_prefix(), new_prefix);
    }
}

void initialize_protected() {
    g_ext     = new protected_ext_reg();
    protected_modification::init();
}

void finalize_protected() {
    protected_modification::finalize();
    delete g_ext;
}
}
