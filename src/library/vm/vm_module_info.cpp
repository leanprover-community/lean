/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include <iostream>
#include <vector>
#include "library/util.h"
#include "library/vm/vm.h"
#include "library/vm/vm_module_info.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_environment.h"

namespace lean {

define_vm_external_core(module_info, std::shared_ptr<module_info const>)

static vm_obj module_info_resolve_module_name(vm_obj const & n_, vm_obj const & cm_) {
    return to_obj(get_global_module_mgr()->resolve(
        module_name(to_name(n_)), to_string(cm_)));
}

static vm_obj module_info_of_module_id(vm_obj const & mi_) {
    return to_obj(get_global_module_mgr()->get_module(to_string(mi_)));
}

static vm_obj module_info_id(vm_obj const & mi_) {
    return to_obj(to_module_info(mi_)->m_id);
}

static vm_obj module_info_get_all() {
    return to_obj(get_global_module_mgr()->get_all_modules());
}

static vm_obj environment_import_dependencies(vm_obj const & env_, vm_obj const & mi_) {
    auto & mod_info = to_module_info(mi_);
    auto env = to_env(env_);

    std::vector<module_name> imports;
    for (auto & dep : mod_info->m_deps) imports.push_back(dep.m_import_name);
    env = import_modules(env, mod_info->m_id, imports, mk_loader(mod_info->m_id, mod_info->m_deps));

    return to_obj(env);
}

static vm_obj environment_import_only(vm_obj const & env_, vm_obj const & mi_) {
    auto & mod_info = to_module_info(mi_);
    auto & loaded_mod = get(mod_info->m_result).m_loaded_module;
    auto env = to_env(env_);
    import_module(loaded_mod->m_modifications, mod_info->m_id, env);
    return to_obj(env);
}

static vm_obj environment_import_only_until_decl(vm_obj const & env_, vm_obj const & mi_, vm_obj const & dn_) {
    auto & mod_info = to_module_info(mi_);
    auto & loaded_mod = get(mod_info->m_result).m_loaded_module;
    auto & decl_name = to_name(dn_);
    auto env = to_env(env_);
    for (auto & modif : loaded_mod->m_modifications) {
        if (auto decl = module::is_decl_modification(*modif.get())) {
            if (decl->get_name() == decl_name) {
                break;
            }
        }
        import_modification(*modif.get(), mod_info->m_id, env);
    }
    return to_obj(env);
}

void initialize_vm_module_info() {
    DECLARE_VM_BUILTIN(name({"module_info", "resolve_module_name"}),   module_info_resolve_module_name);
    DECLARE_VM_BUILTIN(name({"module_info", "of_module_id"}),          module_info_of_module_id);
    DECLARE_VM_BUILTIN(name({"module_info", "id"}),                    module_info_id);
    DECLARE_VM_BUILTIN(name({"module_info", "get_all"}),               module_info_get_all);
    DECLARE_VM_BUILTIN(name({"environment", "import_dependencies"}),   environment_import_dependencies);
    DECLARE_VM_BUILTIN(name({"environment", "import_only"}),           environment_import_only);
    DECLARE_VM_BUILTIN(name({"environment", "import_only_until_decl"}), environment_import_only_until_decl);
}

void finalize_vm_module_info() {
}
}
