/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/type_context.h"
#include "library/trace.h"

namespace lean {

struct simp_result {
    /* Invariant [m_pf : m_orig <rel> m_new] */
    expr m_new;

    /* If proof is not provided, it is assumed to be reflexivity */
    optional<expr> m_proof;

    /* The list of simplification lemmas used in the proof */
    buffer<name> m_lemmas;

    bool m_done{false};
public:
    simp_result() {}
    simp_result(expr const & e): m_new(e) { tout() << "A"; }
    simp_result(expr const & e, expr const & proof, bool done = false): m_new(e), m_proof(proof), m_done(done) { tout() << "B"; }
    simp_result(expr const & e, optional<expr> const & proof): m_new(e), m_proof(proof) { tout() << "C"; }
    simp_result(pair<expr, optional<expr>> const & r): m_new(r.first), m_proof(r.second) { tout() << "D"; }
    simp_result(expr const & e, buffer<name> & lemmas, bool done = false):
      m_new(e), m_lemmas(lemmas), m_done(done) { tout() << "E" << lemmas.size() << "!\n"; }
    simp_result(expr const & e, expr const & proof, buffer<name> & lemmas, bool done = false):
      m_new(e), m_proof(proof), m_lemmas(lemmas), m_done(done) { tout() << "F" << lemmas.size() << "!\n"; }

    bool has_proof() const { return static_cast<bool>(m_proof); }

    expr const & get_new() const { return m_new; }
    expr const & get_proof() const { lean_assert(m_proof); return *m_proof; }
    optional<expr> const & get_optional_proof() const { return m_proof; }
    buffer<name> const & get_lemmas() const { return m_lemmas; }

    /* Push a lemma name to the buffer of simplification lemmas used in the proof */
    void push_lemma(name const & lem) { m_lemmas.push_back(lem); }

    /* The following assumes that [e] and [m_new] are definitionally equal */
    void update(expr const & e) { m_new = e; }

    void set_done() { m_done = true; }
    bool is_done() const { return m_done; }
};

simp_result finalize(type_context_old & tctx, name const & rel, simp_result const & r);
simp_result join(type_context_old & tctx, name const & rel, simp_result const & r1, simp_result const & r2);

simp_result finalize_eq(abstract_type_context & tctx, simp_result const & r);
simp_result join_eq(abstract_type_context & tctx, simp_result const & r1, simp_result const & r2);
}
