/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Mario Carneiro
*/
#pragma once
#include <atomic>
#include <vector>
#include <string>
#include <unordered_map>
#include "library/abstract_parser.h"
#include "library/tactic/tactic_state.h"

namespace lean {

typedef unsigned tactic_state_id;

struct tactic_invocation {
    ast_id m_id;
    tactic_state_id m_start;
    tactic_state_id m_end;
    bool m_success;
    tactic_invocation(ast_id id, tactic_state_id start, tactic_state_id end, bool success):
        m_id(id), m_start(start), m_end(end), m_success(success) {}

#ifdef LEAN_JSON
    operator json() const {
        return {{"ast", m_id}, {"start", m_start}, {"end", m_end}, {"success", m_success}};
    }
#endif
};

class tactic_log {
public:
    struct hyp {
        name m_name;
        name m_pp_name;
        expr m_type;
        optional<expr> m_value;
        unsigned hash() const;
    };
    friend bool operator==(hyp const & t1, hyp const & t2) {
        return t1.m_name == t2.m_name && t1.m_pp_name == t2.m_pp_name &&
            t1.m_type == t2.m_type && t1.m_value == t2.m_value;
    }

    struct goal {
        std::vector<hyp> m_hyps;
        expr m_target_type;
        unsigned hash() const;
    };
    friend bool operator==(goal const & t1, goal const & t2) {
        return t1.m_hyps == t2.m_hyps && t1.m_target_type == t2.m_target_type;
    }

    class summary {
        struct cell {
            name m_decl_name;
            std::vector<goal> m_goals;
            unsigned m_hash;
            MK_LEAN_RC();
            unsigned mk_hash() const;
            cell(name const & decl_name, std::vector<goal> && goals):
                m_decl_name(decl_name), m_goals(std::move(goals)), m_hash(mk_hash()), m_rc(1) {}
            void dealloc() { delete this; }
        };
        friend bool operator==(cell const & c1, cell const & c2) {
            return c1.m_hash == c2.m_hash && c1.m_decl_name == c2.m_decl_name && c1.m_goals == c2.m_goals;
        }

        cell * m_ptr;
        friend struct cell;
        summary(cell * ptr): m_ptr(ptr) {}
        friend bool operator==(summary const & s1, summary const & s2) { return s1.m_ptr == s2.m_ptr || *s1.m_ptr == *s2.m_ptr; }
    public:
        summary(summary const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
        summary(name const & decl_name, std::vector<goal> && goals):
            summary(new cell(decl_name, std::move(goals))) {}
        ~summary() { if (m_ptr) m_ptr->dec_ref(); }
        unsigned hash() const { return m_ptr->m_hash; }
        name decl_name() const { return m_ptr->m_decl_name; }
        std::vector<goal> const & goals() const { return m_ptr->m_goals; }
    };

    struct summary_hash { unsigned operator()(summary const & n) const { return n.hash(); } };
    struct summary_eq { bool operator()(summary const & n1, summary const & n2) const { return n1 == n2; } };

private:
    mutable std::vector<tactic_invocation> m_invocs;
    mutable std::vector<std::string> m_tspps; // tactic state pretty-printeds
    using state_map = std::unordered_map<summary, tactic_state_id, summary_hash, summary_eq>;
    mutable state_map m_state_map;
    mutable std::vector<summary> m_states;
    inline state_map & get_state_map(lock_guard<mutex> &) const { return m_state_map; }

public:
    mutable mutex m_mutex;
    mutable std::atomic_bool m_detached{false};
    mutable std::atomic_bool m_exported{false};
    tactic_log() {}

    tactic_state_id get_id(tactic_state const & ts) const;
    tactic_state_id push_invocation(ast_id id, tactic_state_id start, tactic_state_id end, bool success) const;
    inline std::vector<tactic_invocation> & get_invocs(lock_guard<mutex> &) const { return m_invocs; }
    inline std::vector<std::string> & get_tspps(lock_guard<mutex> &) const { return m_tspps; }
    inline std::vector<summary> & get_states(lock_guard<mutex> &) const { return m_states; }
    void detach() const;
};

class scope_tactic_log {
    tactic_log * m_old_p;
public:
    scope_tactic_log(tactic_log * p);
    ~scope_tactic_log();
};

tactic_log * get_tactic_log();
void log_tactic(ast_id id, tactic_state const & before, tactic_state const & after, bool success);

}
