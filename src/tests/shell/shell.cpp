/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <vector>
#include "util/test.h"
#include "shell/lean_js.h"
#if defined(LEAN_EMSCRIPTEN)
#include <emscripten.h>
#include "shell/emscripten.h"
#endif
using namespace lean;

int main() {
#if defined(LEAN_EMSCRIPTEN)
    LEAN_EMSCRIPTEN_ENV
    LEAN_EMSCRIPTEN_FS
#endif
    save_stack_info();
    initialize_emscripten();
    std::string msg = "{\"seq_num\": 0, \"command\": \"sync\", \"file_name\": \"f\", \"content\": \"inductive f\\ndef g := f\"}";
    emscripten_process_request(reinterpret_cast<uintptr_t>(msg.c_str()));
    msg = "{\"seq_num\": 1, \"command\": \"info\", \"file_name\": \"f\", \"line\": 2, \"column\": 9}";
    emscripten_process_request(reinterpret_cast<uintptr_t>(msg.c_str()));
    finalize_emscripten();
}
