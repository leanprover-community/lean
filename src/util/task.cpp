/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "util/task.h"
#include "util/interrupt.h"

namespace lean {

std::exception_ptr gtask_cell::peek_exception() const {
    if (m_state.load() == task_state::Failed) {
        return m_exception;
    } else {
        return {};
    }
}

void task_queue::wait_for_success(gtask const & t) {
    while (true) {
        switch (t->m_state.load()) {
            case task_state::Success:
                return; // OK
            case task_state::Failed:
                std::rethrow_exception(t->m_exception);
            default:
                wait_for_finish(t);
        }
    }
}

void task_queue::execute(weak_gtask const & t0) {
    auto t = t0.lock();
    if (!t) return;

    lean_always_assert(t);
    lean_always_assert(t->m_state.load() == task_state::Running);
    lean_always_assert(t->m_data);
    lean_always_assert(t->m_data->m_imp);

    try {
        bool did_wait = true;
        while (did_wait) {
            did_wait = false;
            buffer<gtask> deps;
            t->m_data->m_imp->get_dependencies(deps);
            for (auto & dep : deps) {
                if (dep && !dep->peek_is_finished()) {
                    did_wait = true;
                    wait_for_finish(dep);
                }
            }
        }

        auto imp = t->m_data->m_imp;
        t.reset();
        {
            scoped_interrupt_flag _(&imp->m_interrupt);
            imp->execute();
        }

        if (auto t = t0.lock()) {
            t->store();
            t->m_state = task_state::Success;
        }
    } catch (...) {
        if (auto t = t0.lock()) {
            t->m_exception = std::current_exception();
            t->m_state = task_state::Failed;
        }
    }
}

void task_queue::fail(gtask const & t, std::exception_ptr const & ex) {
    lean_always_assert(t->m_state.load() < task_state::Running);

    t->m_exception = ex;
    t->m_state = task_state::Failed;
}

void task_queue::fail(gtask const & t, gtask const & failed) {
    lean_always_assert(failed->m_state.load() == task_state::Failed);

    fail(t, failed->m_exception);
}

void task_queue::submit(gtask const & t, unsigned) {
    return submit(t);
}

static task_queue * g_taskq = nullptr;

void set_task_queue(task_queue * q) {
    if (g_taskq) throw exception("cannot set task queue twice");
    g_taskq = q;
}

task_queue & taskq() {
    return *g_taskq;
}

}
