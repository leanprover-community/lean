/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "util/sstream.h"
#include "kernel/find_fn.h"
#include "kernel/type_checker.h"
#include "kernel/inductive/inductive.h"
#include "library/util.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/user_recursors.h"
#include "library/aux_recursors.h"
#include "library/attribute_manager.h"

namespace lean {
bool recursor_info::is_minor(unsigned pos) const {
    if (pos <= get_motive_pos())
        return false;
    if (get_first_index_pos() <= pos && pos <= m_major_pos)
        return false;
    return true;
}

unsigned recursor_info::get_num_minors() const {
    unsigned r = m_num_args;
    lean_assert(r >= get_motive_pos() + 1);
    r -= (get_motive_pos() + 1);
    lean_assert(m_major_pos >= get_first_index_pos());
    lean_assert(r >= m_major_pos - get_first_index_pos() + 1);
    r -= (m_major_pos - get_first_index_pos() + 1);
    return r;
}

recursor_info::recursor_info(name const & r, name const & I, list<unsigned> const & univ_pos,
                             bool dep_elim, bool is_rec, unsigned num_args, unsigned major_pos,
                             list<optional<unsigned>> const & params_pos, list<unsigned> const & indices_pos,
                             list<bool> const & produce_motive):
    m_recursor(r), m_type_name(I), m_universe_pos(univ_pos), m_dep_elim(dep_elim), m_recursive(is_rec),
    m_num_args(num_args), m_major_pos(major_pos), m_params_pos(params_pos), m_indices_pos(indices_pos),
    m_produce_motive(produce_motive) {}
recursor_info::recursor_info() {}

void recursor_info::write(serializer & s) const {
    s << m_recursor << m_type_name << m_dep_elim << m_recursive << m_num_args << m_major_pos;
    write_list(s, m_universe_pos);
    write_list(s, m_params_pos);
    write_list(s, m_indices_pos);
    write_list(s, m_produce_motive);
}

recursor_info recursor_info::read(deserializer & d) {
    recursor_info info;
    d >> info.m_recursor >> info.m_type_name >> info.m_dep_elim >> info.m_recursive
      >> info.m_num_args >> info.m_major_pos;
    info.m_universe_pos   = read_list<unsigned>(d);
    info.m_params_pos     = read_list<optional<unsigned>>(d);
    info.m_indices_pos    = read_list<unsigned>(d);
    info.m_produce_motive = read_list<bool>(d);
    return info;
}

static void throw_invalid_motive(expr const & C) {
    throw exception(sstream() << "invalid user defined recursor, motive '" << C
                    << "' must have a type of the form (C : Pi (i : B A), I A i -> Type), "
                    "where A is (possibly empty) sequence of bound variables (aka parameters), "
                    "(i : B A) is a (possibly empty) telescope (aka indices), "
                    "and I is a constant");
}

recursor_info mk_recursor_info(environment const & env, name const & r, optional<unsigned> const & _given_major_pos) {
    /* The has_given_major_pos/given_major_pos hack is used to workaround a g++ false warning.
       Note that the pragma
          #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
       doesn't fix the problem here since the uninitialized variable is reported in an inlined buffer method.
       I think it would be even hackier to put the pragma at buffer.h */
    bool has_given_major_pos = static_cast<bool>(_given_major_pos);
    unsigned given_major_pos = 0;
    if (_given_major_pos) given_major_pos = *_given_major_pos;
    if (auto I = inductive::is_elim_rule(env, r)) {
        unsigned num_univ_params = env.get(*I).get_num_univ_params();
        list<unsigned> universe_pos = mk_list_range(0, num_univ_params);
        if (env.get(name(*I, "rec")).get_num_univ_params() != num_univ_params)
            universe_pos = cons(recursor_info::get_motive_univ_idx(), universe_pos);
        bool is_rec                = is_recursive_datatype(env, *I);
        unsigned major_pos         = *inductive::get_elim_major_idx(env, r);
        unsigned num_indices       = *inductive::get_num_indices(env, *I);
        unsigned num_params        = *inductive::get_num_params(env, *I);
        unsigned num_minors        = *inductive::get_num_minor_premises(env, *I);
        unsigned num_args          = num_params + 1 /* motive */ + num_minors + num_indices + 1 /* major */;
        list<bool> produce_motive;
        for (unsigned i = 0; i < num_minors; i++)
            produce_motive = cons(true, produce_motive);
        list<optional<unsigned>> params_pos = map2<optional<unsigned>>(mk_list_range(0, num_params),
                                                                       [](unsigned i) { return optional<unsigned>(i); });
        list<unsigned> indices_pos = mk_list_range(num_params, num_params + num_indices);
        return recursor_info(r, *I, universe_pos, inductive::has_dep_elim(env, *I), is_rec,
                             num_args, major_pos, params_pos, indices_pos, produce_motive);
    } else if (is_aux_recursor(env, r) &&
               (strcmp(r.get_string(), "cases_on") == 0 ||
                strcmp(r.get_string(), "dcases_on") == 0 ||
                strcmp(r.get_string(), "drec_on") == 0 ||
                strcmp(r.get_string(), "rec_on") == 0   ||
                strcmp(r.get_string(), "brec_on") == 0)) {
        name I = r.get_prefix();
        unsigned num_indices  = *inductive::get_num_indices(env, I);
        unsigned num_params   = *inductive::get_num_params(env, I);
        has_given_major_pos   = true;
        given_major_pos       = num_params + 1 /* motive */ + num_indices;
    }
    declaration d = env.get(r);
    type_checker tc(env);
    buffer<expr> tele;
    expr rtype    = to_telescope(tc, d.get_type(), tele);
    buffer<expr> C_args;
    expr C        = get_app_args(rtype, C_args);
    if (!is_local(C) || !std::all_of(C_args.begin(), C_args.end(), is_local)) {
        throw exception("invalid user defined recursor, result type must be of the form (C t), "
                        "where C is a bound variable, and t is a (possibly empty) sequence of bound variables");
    }

    // Compute number of parameters.
    // We assume a parameter is anything that occurs before the motive.
    unsigned num_params  = 0;
    for (expr const & x : tele) {
        if (mlocal_name(x) == mlocal_name(C))
            break;
        num_params++;
    }

    // Locate major premise, and check whether the recursor supports dependent elimination or not.
    expr major;
    unsigned major_pos = 0;
    bool dep_elim;
    if (has_given_major_pos) {
        if (given_major_pos >= tele.size())
            throw exception(sstream() << "invalid user defined recursor, invalid major premise position, "
                            "recursor has only " << tele.size() << "arguments");
        major_pos = given_major_pos;
        major     = tele[major_pos];
        if (!C_args.empty() && tc.is_def_eq(C_args.back(), major))
            dep_elim = true;
        else
            dep_elim = false;
    } else if (C_args.empty()) {
        throw exception(sstream() << "invalid user defined recursor, '" << r << "' does not support dependent elimination, "
                        << "and position of the major premise was not specified "
                        << "(solution: set attribute '[recursor <pos>]', where <pos> is the position of the major premise)");
    } else {
        major    = C_args.back();
        dep_elim = true;
        for (expr const & x : tele) {
            if (tc.is_def_eq(x, major))
                break;
            major_pos++;
        }
    }

    // Number of indices
    unsigned num_indices = C_args.size();
    if (dep_elim)
        num_indices--; // when we have dependent elimination, the last element is the major premise.
    if (major_pos < num_indices)
        throw exception(sstream() << "invalid user defined recursor, indices must occur before major premise '"
                        << major << "'");

    buffer<expr> I_args;
    expr I = get_app_args(mlocal_type(major), I_args);
    if (!is_constant(I)) {
        throw exception(sstream() << "invalid user defined recursor, type of the major premise '" << major
                        << "' must be for the form (I ...), where I is a constant");
    }

    // Store position of the recursor parameters in the major premise.
    buffer<optional<unsigned>> params_pos;
    for (unsigned i = 0; i < num_params; i++) {
        expr const & A = tele[i];
        unsigned j = 0;
        for (; j < I_args.size(); j++) {
            if (tc.is_def_eq(I_args[j], A))
                break;
        }
        if (j == I_args.size()) {
            if (local_info(tele[i]).is_inst_implicit()) {
                params_pos.push_back(optional<unsigned>());
            } else {
                throw exception(sstream() << "invalid user defined recursor, type of the major premise '" << major
                                << "' does not contain the recursor parameter '" << A << "'");
            }
        } else {
            params_pos.push_back(optional<unsigned>(j));
        }
    }

    // Store position of the recursor indices in the major premise
    buffer<unsigned> indices_pos;
    for (unsigned i = major_pos - num_indices; i < major_pos; i++) {
        expr const & idx = tele[i];
        unsigned j = 0;
        for (; j < I_args.size(); j++) {
            if (tc.is_def_eq(I_args[j], idx))
                break;
        }
        if (j == I_args.size()) {
            throw exception(sstream() << "invalid user defined recursor, type of the major premise '" << major
                            << "' does not contain the recursor index '" << idx << "'");
        }
        indices_pos.push_back(j);
    }


    buffer<expr> C_tele;
    expr C_rtype  = to_telescope(tc, mlocal_type(C), C_tele);
    if (!is_sort(C_rtype) || C_tele.size() != C_args.size()) {
        throw_invalid_motive(C);
    }

    level motive_lvl = sort_level(C_rtype);
    // Remark: if we are in the standard environment, then the motive may be a proposition, and be fixed at 0.
    // The following pragma is for avoiding gcc bogus warning
    if (!is_zero(motive_lvl)) {
        if (!is_param(motive_lvl)) {
            throw exception("invalid user defined recursor, "
                            "motive result sort must be Prop or Type.{l} where l is a universe parameter");
        }
    }

    // A universe parameter must occur in the major premise or in the motive
    buffer<unsigned> univ_param_pos;
    for (name const & p : d.get_univ_params()) {
        if (!is_zero(motive_lvl) && param_id(motive_lvl) == p) {
            univ_param_pos.push_back(recursor_info::get_motive_univ_idx());
        } else {
            bool found = false;
            unsigned i = 0;
            for (level const & l : const_levels(I)) {
                if (is_param(l) && param_id(l) == p) {
                    univ_param_pos.push_back(i);
                    found = true;
                    break;
                }
                i++;
            }
            if (!found) {
                throw exception(sstream() << "invalid user defined recursor, major premise '"
                                << major << "' does not contain universe parameter '" << p << "'");
            }
        }
    }

    buffer<bool> produce_motive;
    unsigned nparams  = params_pos.size();
    unsigned nindices = indices_pos.size();
    bool is_rec       = false;
    for (unsigned i = nparams+1; i < tele.size(); i++) {
        if (i < major_pos - nindices || i > major_pos) {
            // i is a minor premise
            buffer<expr> minor_args;
            expr res = get_app_fn(to_telescope(tc, mlocal_type(tele[i]), minor_args));
            if (!is_rec) {
                for (expr const & minor_arg : minor_args) {
                    lean_assert(is_local(minor_arg));
                    if (find(mlocal_type(minor_arg), [&](expr const & e, unsigned) {
                                return is_local(e) && mlocal_name(C) == mlocal_name(e);
                            })) {
                        is_rec = true;
                        break;
                    }
                }
            }
            if (is_local(res) && mlocal_name(C) == mlocal_name(res)) {
                produce_motive.push_back(true);
            } else {
                produce_motive.push_back(false);
            }
        }
    }

    return recursor_info(r, const_name(I), to_list(univ_param_pos), dep_elim, is_rec, tele.size(), major_pos,
                         to_list(params_pos), to_list(indices_pos), to_list(produce_motive));
}

struct recursor_state {
    name_map<recursor_info> m_recursors;
    name_map<list<name>>    m_type2recursors;

    void insert(recursor_info const & info) {
        m_recursors.insert(info.get_name(), info);
        if (auto l = m_type2recursors.find(info.get_type_name())) {
            m_type2recursors.insert(info.get_type_name(),
                                    cons(info.get_name(),
                                         filter(*l, [&](name const & n) { return n != info.get_name(); })));
        } else {
            m_type2recursors.insert(info.get_type_name(), to_list(info.get_name()));
        }
    }
};

struct recursor_config {
    typedef recursor_state  state;
    typedef recursor_info   entry;

    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        s.insert(e);
    }
    static const char * get_serialization_key() { return "UREC"; }
    static void  write_entry(serializer & s, entry const & e) {
        e.write(s);
    }
    static void  textualize_entry(tlean_exporter &, entry const &) {}

    static entry read_entry(deserializer & d) {
        return recursor_info::read(d);
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        return some(e.get_name().hash());
    }
};

template class scoped_ext<recursor_config>;
typedef scoped_ext<recursor_config> recursor_ext;

environment add_user_recursor(environment const & env, name const & r, optional<unsigned> const & major_pos,
                              bool persistent) {
    if (inductive::is_elim_rule(env, r))
        throw exception(sstream() << "invalid user defined recursor, '" << r << "' is a builtin recursor");
    recursor_info info = mk_recursor_info(env, r, major_pos);
    return recursor_ext::add_entry(env, get_dummy_ios(), info, persistent);
}

recursor_info get_recursor_info(environment const & env, name const & r) {
    if (auto info = recursor_ext::get_state(env).m_recursors.find(r))
        return *info;
    return mk_recursor_info(env, r, optional<unsigned>());
}

list<name> get_recursors_for(environment const & env, name const & I) {
    if (auto l = recursor_ext::get_state(env).m_type2recursors.find(I))
        return *l;
    else
        return list<name>();
}

bool is_user_defined_recursor(environment const & env, name const & r) {
    return recursor_ext::get_state(env).m_recursors.find(r) != nullptr;
}

has_recursors_pred::has_recursors_pred(environment const & env):
    m_type2recursors(recursor_ext::get_state(env).m_type2recursors) {}

static indices_attribute const & get_recursor_attribute() {
    return static_cast<indices_attribute const &>(get_system_attribute("recursor"));
}

void initialize_user_recursors() {
    recursor_ext::initialize();
    register_system_attribute(indices_attribute("recursor", "user defined recursor",
                                                [](environment const & env, io_state const &, name const & n, unsigned,
                                                   bool persistent) {
                                                    auto const & data = *get_recursor_attribute().get(env, n);
                                                    if (data.m_idxs && tail(data.m_idxs))
                                                        throw exception(sstream()
                                                                                << "invalid [recursor] declaration, expected at most one parameter");
                                                    return add_user_recursor(env, n, head_opt(data.m_idxs), persistent);
                                                }));
}

void finalize_user_recursors() {
    recursor_ext::finalize();
}
}
