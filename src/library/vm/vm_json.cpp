/*
Copyright (c) E.W.Ayers 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
*/

#include "frontends/lean/json.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_int.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_float.h"
#include "library/vm/vm_option.h"
#include <string>

namespace lean {

enum json_idx {
    vstring = 0,
    vint = 1,
    vfloat = 2,
    vbool = 3,
    vnull = 4,
    vobject = 5,
    varray = 6,
};

json to_json(vm_obj const & o) {
  switch (cidx(o)) {
    case json_idx::vstring: {
        std::string s = to_string(cfield(o, 0));
        return json(s);
    } case json_idx::vint: {
        auto oval = cfield(o, 0);
        if (is_simple(oval)) {
            return json(to_int(oval));
        }
        auto m = to_mpz(oval);
        if (m.is<uint64_t>()) {
            return json(static_cast<uint64_t>(m));
        } else if (m.is<int64_t>()) {
            return json(static_cast<int64_t>(m));
        } else {
            // lose precision and store as a double, because that's how the nlohmann/json
            // parser behaves anyway.
            return json(m.get_double());
        }
    } case json_idx::vfloat: {
        float f = to_float(cfield(o, 0));
        return json(f);
    } case json_idx::vbool: {
        bool b = to_bool(cfield(o, 0));
        return json(b);
    } case json_idx::vnull: {
        return json(nullptr);
    } case json_idx::vobject: {
        json j = json::object();
        vm_obj l = cfield(o, 0);
        while (!is_simple(l)) {
            vm_obj h = head(l);
            std::string key = to_string(cfield(h, 0));
            json value = to_json(cfield(h, 1));
            j[key] = value;
            l = tail(l);
        }
        return j;
    } case json_idx::varray: {
        json j = json::array();
        vm_obj l = cfield(o, 0);
        while (!is_simple(l)) {
            j.push_back(to_json(head(l)));
            l = tail(l);
        }
        return j;
    } default: {
        lean_unreachable();
        break;
  }}
}

vm_obj to_obj(json const & j) {
    if (j.is_null()) {
        return mk_vm_simple(json_idx::vnull);
    } else if (j.is_boolean()) {
        return mk_vm_constructor(json_idx::vbool, mk_vm_bool(j));
    } else if (j.is_number_float()) {
        // note that this throws away a lot of precision, as the vm floats are not doubles
        auto f = j.get<double>();
        return mk_vm_constructor(json_idx::vfloat, to_obj(f));
    } else if (j.is_number_unsigned()) {
        auto i = j.get<std::uint64_t>();
        return mk_vm_constructor(json_idx::vint, mk_vm_int(i));
    } else if (j.is_number_integer()) {
        auto i = j.get<std::int64_t>();
        return mk_vm_constructor(json_idx::vint, mk_vm_int(i));
    } else if (j.is_string()) {
        std::string s = j;
        return mk_vm_constructor(json_idx::vstring, to_obj(s));
    } else if (j.is_array()) {
        vm_obj o = mk_vm_nil();
        for (auto i = j.crbegin(); i != j.crend(); i++) {
          o = mk_vm_cons(to_obj(*i), o);
        }
        return mk_vm_constructor(json_idx::varray, o);
    } else if (j.is_object()) {
        vm_obj o = mk_vm_nil();
        for (auto el = j.crbegin(); el != j.crend(); el++) {
            o = mk_vm_cons(mk_vm_pair(
                    to_obj(el.key()),
                    to_obj(el.value())), o);
        }
        return mk_vm_constructor(json_idx::vobject, o);
    } else {
        lean_unreachable();
    }
}

vm_obj parse(vm_obj const & s) {
    try {
        json j = json::parse(to_string(s));
        return mk_vm_some(to_obj(j));
    } catch(...) {
        return mk_vm_none();
    }
}

vm_obj unparse(vm_obj const & o) {
    return to_obj(to_json(o).dump());
}

void initialize_vm_json() {
    DECLARE_VM_BUILTIN(name({"json", "parse"}), parse);
    DECLARE_VM_BUILTIN(name({"json", "unparse"}), unparse);
}
void finalize_vm_json() {}

}
