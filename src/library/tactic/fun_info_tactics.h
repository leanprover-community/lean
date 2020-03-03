/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
namespace lean {
vm_obj to_obj(fun_info const & info);
void initialize_fun_info_tactics();
void finalize_fun_info_tactics();
}
