/*
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Simon Hudon
*/

#include <map>
#include "kernel/environment.h"
#include "library/module.h"
#include "library/vm/vm.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_option.h"
#include "library/kernel_serializer.h"

namespace lean {

struct eqn_info : public environment_extension {
    std::map<name, expr> m_eqn_info;

    eqn_info() { }
};

struct eqn_info_reg {
    unsigned                  m_ext_id;
    eqn_info_reg() {
        m_ext_id     = environment::register_extension(std::make_shared<eqn_info>(eqn_info()));
    }
};

static eqn_info_reg * g_ext = nullptr;

static eqn_info const & get_extension(environment const & env) {
    return static_cast<eqn_info const &>(env.get_extension(g_ext->m_ext_id));
}

static environment update(environment const & env, eqn_info const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<eqn_info>(ext));
}


struct eqn_info_modification : public modification {
    LEAN_MODIFICATION("EQN_INFO")

    name     m_fn;
    expr     m_eqns;

    eqn_info_modification(name const & fn, expr const & eqns): m_fn(fn), m_eqns(eqns) {}

    void perform(environment & env) const override {
        auto ext = get_extension(env);
        ext.m_eqn_info.insert(mk_pair(m_fn, m_eqns));
        env = update(env, ext);
    }

    void serialize(serializer & s) const override {
        s << m_fn << m_eqns;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        name fn; expr eqns;
        d >> fn >> eqns;
        return std::make_shared<eqn_info_modification>(fn, eqns);
    }
};

optional<expr> get_eqn_spec(environment const & env, name const & n) {
    auto ext = get_extension(env);
    std::map<name, expr>::iterator eqn = ext.m_eqn_info.find(n);
    if (eqn != ext.m_eqn_info.end()) {
        return optional<expr>(eqn->second);
    } else {
        return optional<expr>();
    }
}

vm_obj environment_get_eqn_spec(vm_obj const & env, vm_obj const & n) {
    environment env_ = to_env(env);
    name n_ = to_name(n);
    if (auto r = get_eqn_spec(env_, n_)) {
        return mk_vm_some(to_obj(*r));
    } else {
        return mk_vm_none();
    }
}

environment store_eqn_spec(environment const & env, name const & n, expr const & e) {
    return module::add_and_perform(env, std::make_shared<eqn_info_modification>(n, e));
}

void initialize_eqn_api() {
    g_ext = new eqn_info_reg();
    eqn_info_modification::init();
    DECLARE_VM_BUILTIN(name({"environment", "defn_spec"}),        environment_get_eqn_spec);
}

void finalize_eqn_api() {
    eqn_info_modification::finalize();
    delete g_ext;
}


}
