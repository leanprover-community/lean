/*
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <cmath>
#include <functional>
#include <unordered_map>
#include <unordered_set>
#include "kernel/expr_maps.h"
#include "kernel/expr_sets.h"
#include "kernel/for_each_fn.h"
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "library/constants.h"
#include "library/feature_search.h"
#include "library/predict/predict.h"
#include "library/type_context.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_float.h"
#include "library/vm/vm.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "util/name.h"
#include "util/name_hash_set.h"

namespace lean {

struct feature {
    feature(name const & n) : m_name(n) {}
    feature(name const & n, name const & p) : m_name(n), m_parent(p) {}

    name m_name;
    optional<name> m_parent;

    bool operator==(feature const & that) const noexcept {
        return m_name == that.m_name && m_parent == that.m_parent;
    }
};

}

template <> struct std::hash<lean::feature> {
    std::size_t operator()(lean::feature const & f) const noexcept {
        return f.m_name.hash() ^ (16777619 * (f.m_parent ? f.m_parent->hash() : 0));
    }
};

namespace lean {

using feature_vec = std::vector<feature>;

feature_vec isect(feature_vec const & a, feature_vec const & b);
feature_vec union_(feature_vec const & a, feature_vec const & b);

struct feature_cfg {
    bool m_ignore_tc = true;
    bool m_ignore_pi_domain = true;
    bool m_ignore_type_args = true;
    bool m_ignore_decidable = true;
    bool m_ignore_conns = true;
};

struct feature_collector {
    type_context_old & m_ctx;

    name_hash_set m_ignored_consts;
    name_hash_set m_ignored_preds;
    feature_cfg m_cfg;

    feature_vec operator()(expr const & thm);

    feature_collector(type_context_old & ctx, feature_cfg const & cfg);

    friend struct collect_visitor;
};

feature_vec feature_vec_of(type_context_old & ctx, expr const & e);

struct feature_stats {
    unsigned m_thms;
    std::unordered_map<feature, unsigned> m_feature_counts;

    void add(feature_vec const & fv);

    float idf(feature const & f) const;

    float norm(feature_vec const & f) const;

    float dotp(feature_vec const & a, feature_vec const & b) const;

    float cosine_similarity(feature_vec const & a, feature_vec const & b) const;
};

class vm_obj;
vm_obj to_obj(feature const & f);
feature to_feature(vm_obj const & o);
vm_obj to_obj(feature_vec const & feat_vec);
feature_vec const & to_feature_vec(vm_obj const & o);
feature_vec isect(feature_vec const & a, feature_vec const & b) {
    std::unordered_set<feature> a_set(a.begin(), a.end());
    feature_vec result;
    for (auto & x : b) if (a_set.count(x)) result.push_back(x);
    return result;
}

feature_vec union_(feature_vec const & a, feature_vec const & b) {
    std::unordered_set<feature> a_set(a.begin(), a.end());
    feature_vec result(a.begin(), a.end());
    for (auto & x : b) if (!a_set.count(x)) result.push_back(x);
    return result;
}

feature_collector::feature_collector(type_context_old & ctx, feature_cfg const & cfg)
        : m_ctx(ctx), m_cfg(cfg) {
    auto i = [&] (name const & n) { m_ignored_consts.insert(n); };
    if (m_cfg.m_ignore_conns) {
        i(get_eq_name());
        i(get_ne_name());
        i(get_heq_name());
        i(get_Exists_name());
        i(get_iff_name());
        i(get_not_name());
        i(get_and_name());
        i(get_or_name());
    }

    auto j = [&] (name const & n) { m_ignored_preds.insert(n); };
    if (m_cfg.m_ignore_decidable) {
        j(get_decidable_name());
        j({"decidable_eq"});
        j({"decidable_rel"});
        j({"decidable_pred"});
    }
}

struct collect_visitor {
    feature_collector & m_collector;
    std::unordered_set<feature> m_feats;
    expr_set m_visited;

    type_context_old & ctx() { return m_collector.m_ctx; }
    feature_cfg & cfg() { return m_collector.m_cfg; }

    bool ignored(name const & n) { return !!m_collector.m_ignored_consts.count(n); }
    bool ignored_pred(name const & n) { return !!m_collector.m_ignored_preds.count(n); }

    void visit_let(expr const & e) {
        visit(let_value(e));
        visit(let_type(e));
        visit(let_body(e));
    }

    void visit_macro(expr const & e) {
        for (unsigned i = 0; i < macro_num_args(e); i++)
            visit(macro_arg(e, i));
    }

    void visit_pi(expr const & e0) {
        if (!cfg().m_ignore_pi_domain || !has_free_var(binding_body(e0), 0)) {
            // only visit lhs of implications
            visit(binding_domain(e0));
        }
        visit(binding_body(e0));
    }

    void visit_lambda(expr const & e0) {
        visit(binding_domain(e0));
        visit(binding_body(e0));
    }

    void visit_fn(expr const & e) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        optional<name> fn_sym;
        expr fn_ty;
        switch (fn.kind()) {
            case expr_kind::Constant:
                if (ignored_pred(const_name(fn)))
                    return;
                if (!ignored(const_name(fn)))
                    m_feats.insert(feature(const_name(fn)));
                fn_sym = some(const_name(fn));
                fn_ty = ctx().env().get(const_name(fn)).get_type();
                break;
            case expr_kind::Local:
                break;
            case expr_kind::App:
                lean_unreachable();
                break;
            default:
                visit(fn);
        }
        if (args.empty()) return;
        for (size_t i = 0; i < args.size(); i++) {
            if (is_pi(fn_ty)) {
                auto bi = binding_info(fn_ty);
                auto & bd = binding_domain(fn_ty);
                fn_ty = binding_body(fn_ty);
                if (cfg().m_ignore_tc && bi.is_inst_implicit()) {
                    // ignore implicit arguments
                    continue;
                }
                if (cfg().m_ignore_type_args && is_sort(bd) && has_free_var(fn_ty, 0)) {
                    // ignore arguments for type polymorphism
                    continue;
                }
            }
            visit(args[i]);
            if (fn_sym) {
                expr const & arg_fn_sym = get_app_fn(args[i]);
                if (is_constant(arg_fn_sym) &&
                        !ignored(*fn_sym) &&
                        !ignored(const_name(arg_fn_sym))) {
                    m_feats.insert(feature(const_name(arg_fn_sym), *fn_sym));
                }
            }
        }
    }

    void visit(expr const & e) {
        if (m_visited.find(e) != m_visited.end())
            return;
        m_visited.insert(e);
        switch (e.kind()) {
        case expr_kind::Meta:
        case expr_kind::Sort:
            break; /* do nothing */
        case expr_kind::Var:
            break;
        case expr_kind::Macro:
            return visit_macro(e);
        case expr_kind::Lambda:
            return visit_lambda(e);
        case expr_kind::Pi:
            return visit_pi(e);
        case expr_kind::Let:
            return visit_let(e);
        case expr_kind::Local:
        case expr_kind::App:
        case expr_kind::Constant:
            return visit_fn(e);
        }
    }

    collect_visitor(feature_collector & coll) : m_collector(coll) {}

    feature_vec to_vector() {
        return std::vector<feature>(m_feats.begin(), m_feats.end());
    }
};

feature_vec feature_collector::operator()(expr const & thm) {
    collect_visitor collector(*this);
    collector.visit(thm);
    return collector.to_vector();
}

feature_vec feature_vec_of(type_context_old & ctx, expr const & e, feature_cfg const & cfg) {
    feature_collector collector(ctx, cfg);
    return collector(e);
}

void feature_stats::add(feature_vec const & fv) {
    m_thms++;
    for (auto & feat : fv) {
        m_feature_counts[feat] += 1;
    }
}

float feature_stats::idf(feature const & f) const {
    auto it = m_feature_counts.find(f);
    unsigned num_thms = 1 + (it == m_feature_counts.end() ? 0 : it->second);
    return log(m_thms / float(num_thms));
}

float feature_stats::norm(feature_vec const & a) const {
    float sq_norm = 0;
    for (auto & f : a) {
        float idf_ = idf(f);
        sq_norm += idf_ * idf_;
    }
    return sqrt(sq_norm);
}

float feature_stats::dotp(feature_vec const & a, feature_vec const & b) const {
    float dotp = 0;
    std::unordered_set<feature> b_feats(b.begin(), b.end());
    for (auto & f : a) {
        if (b_feats.count(f)) {
            auto idf_ = idf(f);
            dotp += idf_ * idf_;
        }
    }
    return dotp;
}

float feature_stats::cosine_similarity(feature_vec const & a, feature_vec const & b) const {
    return dotp(a,b) / norm(a) / norm(b);
}

struct predictor {
    std::unique_ptr<::predictor> m_predictor;

    std::unordered_map<name, long, name_hash, name_eq> m_thms;
    std::vector<name> m_thm_names;

    std::unordered_map<feature, long> m_feats;
    long m_feat_cnt = 0;

    long of_thm(name const & n) {
        auto it = m_thms.find(n);
        if (it != m_thms.end()) {
            return it->second;
        }
        long i = m_thm_names.size();
        m_thm_names.push_back(n);
        m_thms[n] = i;
        return i;
    }

    long of_feature(feature const & f) {
        auto it = m_feats.find(f);
        if (it != m_feats.end()) {
            return it->second;
        }
        long i = m_feat_cnt++;
        m_feats[f] = i;
        return i;
    }

    std::vector<std::pair<name, double>> predict(feature_vec const & fv, unsigned num_results) {
        std::vector<long> fv_; fv_.reserve(fv.size());
        for (auto & f : fv) {
            auto it = m_feats.find(f);
            if (it != m_feats.end()) {
                fv_.push_back(it->second);
            }
        }
        auto thm_idxs = m_predictor->predict(fv_, num_results);
        std::vector<std::pair<name, double>> thms; thms.reserve(thm_idxs.size());
        for (auto & thm_idx : thm_idxs) {
            thms.push_back({m_thm_names.at(thm_idx.first), thm_idx.second});
        }
        return thms;
    }
};

std::shared_ptr<predictor> mk_predictor(environment const & env, predictor_type type, feature_cfg const & cfg) {
    type_context_old tc(env);
    feature_collector fc(tc, cfg);
    auto p = std::make_shared<predictor>();
    std::vector<std::vector<long>> deps;
    std::vector<std::vector<long>> syms;
    env.for_each_declaration([&] (declaration const & decl) {
        if (!decl.is_trusted()) return;
        optional<expr> value;
        if (decl.is_definition()) {
            value = decl.get_value();
        } else if (decl.is_theorem()) {
            value = peek(decl.get_value_task());
        }

        long i = p->of_thm(decl.get_name());
        if (static_cast<size_t>(i) >= deps.size()) {
            deps.resize(i+1);
            syms.resize(i+1);
        }

        auto & ss = syms[i];
        for (auto & f : fc(decl.get_type())) ss.push_back(p->of_feature(f));

        name_hash_set ds;
        ds.insert(decl.get_name());
        if (value) {
            for_each(*value, [&] (expr const & e, unsigned) {
                if (is_constant(e)) {
                    ds.insert(const_name(e));
                }
                return true;
            });
        }
        auto & ds_ = deps[i];
        for (auto & d : ds) ds_.push_back(p->of_thm(d));
    });
    p->m_predictor.reset(new ::predictor(type, deps, syms));
    p->m_predictor->learn_all();
    return p;
}

vm_obj to_obj(feature const & f) {
    if (f.m_parent) {
        return mk_vm_constructor(1, to_obj(*f.m_parent), to_obj(f.m_name));
    } else {
        return mk_vm_constructor(0, to_obj(f.m_name));
    }
}

feature to_feature(vm_obj const & o) {
    if (cidx(o) == 0) {
        return feature(to_name(cfield(o, 0)));
    } else {
        return feature(to_name(cfield(o, 1)), to_name(cfield(o, 0)));
    }
}

predictor_type to_predictor_type(vm_obj const & o) {
    switch (cidx(o)) {
        case 0: return predictor_type::KNN;
        case 1: return predictor_type::MEPO;
        case 2: return predictor_type::BAYES;
        default: vm_check_failed("unknown value for predictor_type");
    }
}

feature_cfg to_feature_cfg(vm_obj const & o) {
    feature_cfg cfg;
    cfg.m_ignore_tc = to_bool(cfield(o, 0));
    cfg.m_ignore_pi_domain = to_bool(cfield(o, 1));
    cfg.m_ignore_type_args = to_bool(cfield(o, 2));
    cfg.m_ignore_decidable = to_bool(cfield(o, 3));
    cfg.m_ignore_conns = to_bool(cfield(o, 4));
    return cfg;
}

define_vm_external(feature_vec)

static vm_obj feature_vec_isect(vm_obj const & a_, vm_obj const & b_) {
    return to_obj(isect(to_feature_vec(a_), to_feature_vec(b_)));
}

static vm_obj feature_vec_union(vm_obj const & a_, vm_obj const & b_) {
    return to_obj(union_(to_feature_vec(a_), to_feature_vec(b_)));
}

static vm_obj feature_vec_of_expr(vm_obj const & env_, vm_obj const & e_, vm_obj const & cfg_) {
    auto & env = to_env(env_);
    type_context_old ctx(env);
    auto & e = to_expr(e_);
    auto fv = feature_vec_of(ctx, e, to_feature_cfg(cfg_));
    return to_obj(std::move(fv));
}

static vm_obj feature_vec_of_exprs(vm_obj const & env_, vm_obj const & es_, vm_obj const & cfg_) {
    auto & env = to_env(env_);
    type_context_old ctx(env);
    feature_collector collector(ctx, to_feature_cfg(cfg_));

    buffer<vm_obj> fvs;
    vm_obj const * iter = &es_;
    while (!is_nil(*iter)) {
        expr const & e = to_expr(cfield(*iter, 0));
        fvs.push_back(to_obj(collector(e)));
        iter = &cfield(*iter, 1);
    }

    return to_obj(fvs);
}

static vm_obj feature_vec_to_list(vm_obj const & fv_) {
    auto & fv = to_feature_vec(fv_);
    buffer<vm_obj> feats;
    for (auto & f : fv) feats.push_back(to_obj(f));
    return to_obj(feats);
}

define_vm_external(feature_stats)

static vm_obj feature_stats_of_feature_vecs(vm_obj const & fvs_) {
    feature_stats stats;
    vm_obj const * iter = &fvs_;
    while (!is_nil(*iter)) {
        feature_vec const & fv = to_feature_vec(cfield(*iter, 0));
        stats.add(fv);
        iter = &cfield(*iter, 1);
    }
    return to_obj(std::move(stats));
}

static vm_obj feature_stats_idf(vm_obj const & fs_, vm_obj const & f_) {
    return to_obj(to_feature_stats(fs_).idf(to_feature(f_)));
}

static vm_obj feature_stats_dotp(vm_obj const & fs_, vm_obj const & fv1_, vm_obj const & fv2_) {
    return to_obj(to_feature_stats(fs_).dotp(to_feature_vec(fv1_), to_feature_vec(fv2_)));
}

static vm_obj feature_stats_norm(vm_obj const & fs_, vm_obj const & fv_) {
    return to_obj(to_feature_stats(fs_).norm(to_feature_vec(fv_)));
}

static vm_obj feature_stats_cosine_similarity(vm_obj const & fs_, vm_obj const & fv1_, vm_obj const & fv2_) {
    return to_obj(to_feature_stats(fs_).cosine_similarity(to_feature_vec(fv1_), to_feature_vec(fv2_)));
}

static vm_obj feature_stats_features(vm_obj const & fs_) {
    buffer<vm_obj> feats;
    auto & fs = to_feature_stats(fs_);
    for (auto & entry : fs.m_feature_counts) {
        feats.push_back(to_obj(entry.first));
    }
    return to_obj(feats);
}

define_vm_external_core(predictor, std::shared_ptr<predictor>)

static vm_obj environment_mk_predictor(vm_obj const & env_, vm_obj const & p_cfg_) {
    auto & cfg_ = cfield(p_cfg_, 0);
    auto & type_ = cfield(p_cfg_, 1);
    return to_obj(mk_predictor(to_env(env_), to_predictor_type(type_), to_feature_cfg(cfg_)));
}

static vm_obj predictor_predict(vm_obj const & p_, vm_obj const & fv_, vm_obj const & n_) {
    auto & p = to_predictor(p_);
    auto & fv = to_feature_vec(fv_);
    unsigned n = to_unsigned(n_);
    auto results = p->predict(fv, n);
    buffer<vm_obj> results_;
    for (auto & res : results) {
        results_.push_back(mk_vm_pair(
            to_obj(res.first),
            to_obj(res.second)
        ));
    }
    return to_obj(results_);
}

void initialize_feature_search() {
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_vec", "of_expr"}), feature_vec_of_expr);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_vec", "of_exprs"}), feature_vec_of_exprs);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_vec", "to_list"}), feature_vec_to_list);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_vec", "isect"}), feature_vec_isect);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_vec", "union"}), feature_vec_union);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_stats", "of_feature_vecs"}), feature_stats_of_feature_vecs);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_stats", "idf"}), feature_stats_idf);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_stats", "dotp"}), feature_stats_dotp);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_stats", "norm"}), feature_stats_norm);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_stats", "cosine_similarity"}), feature_stats_cosine_similarity);
    DECLARE_VM_BUILTIN(name({"feature_search", "feature_stats", "features"}), feature_stats_features);
    DECLARE_VM_BUILTIN(name({"environment", "mk_predictor"}), environment_mk_predictor);
    DECLARE_VM_BUILTIN(name({"feature_search", "predictor", "predict"}), predictor_predict);
}

void finalize_feature_search() {}

}
