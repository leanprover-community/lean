/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Mario Carneiro
*/
#include <vector>
#include "util/thread.h"
#include "library/tactic/tactic_log.h"

namespace lean {

unsigned tactic_log::hyp::hash() const {
    auto h = ::lean::hash(::lean::hash(m_name.hash(), m_pp_name.hash()), m_type.hash());
    if (m_value) h = ::lean::hash(h, m_value->hash());
    return h;
}

unsigned tactic_log::goal::hash() const {
    unsigned h = m_hyps.size();
    for (auto& g : m_hyps) h = ::lean::hash(h, g.hash());
    return ::lean::hash(h, m_target_type.hash());
}

unsigned tactic_log::summary::cell::mk_hash() const {
    auto h = ::lean::hash(m_decl_name.hash(), (unsigned) m_goals.size());
    for (auto& g : m_goals) h = ::lean::hash(h, g.hash());
    return h;
}

tactic_state_id tactic_log::get_id(summary const & s) const {
    lock_guard<mutex> l(m_mutex);
    auto& map = get_state_map(l);
    auto it = map.find(s);
    if (it != map.end()) return it->second;
    tactic_state_id r = get_states(l).size();
    get_states(l).push_back(s);
    map.emplace(s, r);
    return r;
}

tactic_state_id tactic_log::push_invocation(ast_id id, tactic_state_id start, tactic_state_id end, bool success) const {
    lock_guard<mutex> l(m_mutex);
    auto& invocs = get_invocs(l);
    tactic_state_id n = invocs.size();
    invocs.emplace_back(id, start, end, success);
    return n;
}

void tactic_log::detach() const {
    if (!m_detached.exchange(true)) {
        lock_guard<mutex> l(m_mutex);
        // reclaim memory
        m_invocs = std::vector<tactic_invocation>();
        m_state_map = state_map();
        m_states = std::vector<summary>();
    }
}

LEAN_THREAD_PTR(tactic_log, g_p);

scope_tactic_log::scope_tactic_log(tactic_log * p):m_old_p(g_p) { g_p = p; }
scope_tactic_log::~scope_tactic_log() { g_p = m_old_p; }

tactic_log * get_tactic_log() { return g_p && !g_p->m_detached ? g_p : nullptr; }

static tactic_log::hyp summarize(local_decl const & d) {
    return {d.get_name(), d.get_pp_name(), d.get_type(), d.get_value()};
}

static tactic_log::goal summarize(metavar_decl const & d) {
    std::vector<tactic_log::hyp> hyps;
    d.get_context().for_each([&] (local_decl const & ld) {
        return hyps.push_back(summarize(ld));
    });
    return {hyps, d.get_type()};
}

static tactic_log::summary summarize(tactic_state const & s) {
    std::vector<tactic_log::goal> goals;
    for (auto& g : s.goals()) goals.push_back(summarize(s.mctx().get_metavar_decl(g)));
    return {s.decl_name(), std::move(goals)};
}

void log_tactic(ast_id id, tactic_state const & before, tactic_state const & after, bool success) {
    if (auto log = get_tactic_log()) {
        lean_assert(!log->m_exported);
        auto s1 = log->get_id(summarize(before));
        auto s2 = is_eqp(before, after) ? s1 : log->get_id(summarize(after));
        log->push_invocation(id, s1, s2, success);
    }
}

}
