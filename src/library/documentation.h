/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <utility>
#include <vector>
#include "kernel/environment.h"
#include "util/message_definitions.h"

namespace lean {
struct mod_doc_entry {
    optional<std::string> m_mod_name;
    list<std::pair<pos_info, std::string>> m_docs;
};
environment add_module_doc_string(environment const & env, std::string doc, pos_info pos);
environment add_doc_string(environment const & env, name const & n, std::string);
optional<std::string> get_doc_string(environment const & env, name const & n);
void get_module_doc_strings(environment const & env, buffer<mod_doc_entry> & result);
void initialize_documentation();
void finalize_documentation();
}
