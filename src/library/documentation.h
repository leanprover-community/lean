/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
namespace lean {
struct mod_doc_entry {
    optional<std::string> m_mod_name;
    std::string           m_doc;
};
environment add_module_doc_string(environment const & env, std::string doc);
environment add_doc_string(environment const & env, name const & n, std::string);
optional<std::string> get_doc_string(environment const & env, name const & n);
void get_module_doc_strings(environment const & env, buffer<mod_doc_entry> & result);
void initialize_documentation();
void finalize_documentation();
}
