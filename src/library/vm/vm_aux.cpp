/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "util/timeit.h"
#include "library/trace.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_nat.h"

namespace lean {
vm_obj vm_timeit(vm_obj const &, vm_obj const & s, vm_obj const & fn) {
    std::string msg = to_string(s);
    timeit timer(tout().get_stream(), msg.c_str());
    return invoke(fn, mk_vm_unit());
}

vm_obj vm_trace(vm_obj const &, vm_obj const & s, vm_obj const & fn) {
    tout() << to_string(s) << "\n";
    return invoke(fn, mk_vm_unit());
}

vm_obj vm_trace_call_stack(vm_obj const &, vm_obj const & fn) {
    auto & s = get_vm_state();
    auto out = tout();
    for (unsigned i = 0; i < s.call_stack_size() - 1; i++) {
        out << s.call_stack_fn(i) << "\n";
    }
    return invoke(fn, mk_vm_unit());
}

vm_obj vm_sorry() {
    auto & s = get_vm_state();
    throw exception(sstream() << s.call_stack_fn(s.call_stack_size() - 1)
                              << ": trying to evaluate sorry");
}

vm_obj vm_undefined_core(vm_obj const &, vm_obj const & message) {
    throw exception(to_string(message));
}

vm_obj vm_try_for(vm_obj const &, vm_obj const & n, vm_obj const & thunk) {
    size_t max  = static_cast<size_t>(force_to_unsigned(n))*1000;
    scope_heartbeat     scope1(0);
    scope_max_heartbeat scope2(max);
    vm_obj unit = mk_vm_unit();
    if (auto r = get_vm_state().try_invoke_catch(thunk, 1, &unit)) {
        return mk_vm_some(*r);
    } else {
        return mk_vm_none();
    }
}

vm_obj vm_try_for_time (vm_obj const &, vm_obj const & n, vm_obj const & thunk) {
  size_t max = static_cast<size_t> (force_to_unsigned(n)); // n = # millisecs, max = # millisecs
  auto ctok = mk_cancellation_token(global_cancellation_token());
  condition_variable wake_up_killer;
  mutex killer_mutex;
  bool finished = false;
  lthread killer([&] () {
    unique_lock<mutex> lock(killer_mutex);
    wake_up_killer.wait_for(lock, chrono::milliseconds(max), [&] { return finished; });
    cancel(ctok);
  });
  scope_cancellation_token scope1(ctok);
  vm_obj unit = mk_vm_unit();
  vm_obj result;
  if (auto r = get_vm_state().try_invoke_catch(thunk, 1, &unit)) {
    result = mk_vm_some(*r);
  } else {
    result = mk_vm_none();
  }
  { unique_lock<mutex> lock(killer_mutex); finished = true; }
  wake_up_killer.notify_one();
  killer.join();
  return result;
}


void initialize_vm_aux() {
    DECLARE_VM_BUILTIN("timeit",           vm_timeit);
    DECLARE_VM_BUILTIN("trace",            vm_trace);
    DECLARE_VM_BUILTIN("trace_call_stack", vm_trace_call_stack);
    DECLARE_VM_BUILTIN("sorry",            vm_sorry);
    DECLARE_VM_BUILTIN("undefined_core",   vm_undefined_core);
    DECLARE_VM_BUILTIN("try_for",          vm_try_for);
    DECLARE_VM_BUILTIN("try_for_time",     vm_try_for_time);
}

void finalize_vm_aux() {
}
}
