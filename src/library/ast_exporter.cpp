/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Mario Carneiro
*/
#include <string>
#include <vector>
#include "library/ast_exporter.h"
#include "frontends/lean/json.h"
#include "frontends/lean/parser.h"
#include "util/file_lock.h"
#include "kernel/expr.h"

namespace lean {

#ifdef LEAN_JSON

struct ast_exporter : abstract_ast_exporter {
    std::vector<ast_data*> const & m_ast;
    tag_ast_table const & m_tag_ast_table;
    tactic_log const * m_tactic_log;
    std::vector<bool> m_reachable;
    json m_levels;
    json m_exprs = {nullptr};
    level_map<unsigned> m_level2idx;
    std::unordered_map<expr_cell*, unsigned> m_expr2idx;

    void mark(ast_id id) {
        if (!m_reachable[id]) {
            m_reachable[id] = true;
            for (ast_id i : m_ast[id]->m_children) mark(i);
        }
    }

    ast_exporter(std::vector<ast_data*> const & ast, tag_ast_table const & tag_ast_table, tactic_log const * log):
        m_ast(ast), m_tag_ast_table(tag_ast_table), m_tactic_log(log),
        m_reachable(ast.size(), false) {
        m_levels.push_back("0");
        m_level2idx.emplace(mk_level_zero(), 0);
        m_reachable[0] = true;
        mark(AST_TOP_ID);
    }

    unsigned export_level(const level & l) override {
        auto it = m_level2idx.find(l);
        if (it != m_level2idx.end()) return it->second;
        json j;
        switch (l.kind()) {
        case level_kind::Zero: lean_unreachable();
        case level_kind::Succ:
            j["suc"] = export_level(succ_of(l)); break;
        case level_kind::Max:
            j["max"] = {export_level(max_lhs(l)), export_level(max_rhs(l))}; break;
        case level_kind::IMax:
            j["imax"] = {export_level(imax_lhs(l)), export_level(imax_rhs(l))}; break;
        case level_kind::Param:
            j["param"] = json_of_name(param_id(l)); break;
        case level_kind::Meta:
            j["mvar"] = json_of_name(meta_id(l)); break;
        }
        auto r = m_levels.size();
        m_levels.push_back(std::move(j));
        m_level2idx.emplace(l, r);
        return r;
    }

    unsigned export_expr(const expr & e) override {
        auto it = m_expr2idx.find(e.raw());
        if (it != m_expr2idx.end()) return it->second;
        json j;
        switch (e.kind()) {
            case expr_kind::Var:
                j["var"] = var_idx(e); break;
            case expr_kind::Sort:
                j["sort"] = export_level(sort_level(e)); break;
            case expr_kind::Meta:
                j["mvar"] = {
                    {"name", json_of_name(mlocal_name(e))},
                    {"pp", json_of_name(mlocal_pp_name(e))},
                    {"type", export_expr(mlocal_type(e))}};
                break;
            case expr_kind::Local:
                j["local"] = {
                    {"name", json_of_name(mlocal_name(e))},
                    {"pp", json_of_name(mlocal_pp_name(e))},
                    {"bi", local_info(e).hash()},
                    {"type", export_expr(mlocal_type(e))}};
                break;
            case expr_kind::Constant: {
                json jl = json::array();
                for (auto l : const_levels(e)) jl += export_level(l);
                j["const"] = {json_of_name(const_name(e)), std::move(jl)};
                break;
            }
            case expr_kind::Macro: {
                auto& jm = j[macro_def(e).get_name().get_string()] = json::object();
                macro_def(e).raw()->write_json(*this, jm);
                auto& jargs = jm["args"] = json::array();
                for (unsigned i = 0; i < macro_num_args(e); i++)
                    jargs += export_expr(macro_arg(e, i));
                break;
            }
            case expr_kind::Lambda:
            case expr_kind::Pi:
                j[(e.kind() == expr_kind::Pi) ? "Pi" : "lam"] = {
                    {"name", json_of_name(binding_name(e))},
                    {"bi", binding_info(e).hash()},
                    {"dom", export_expr(binding_domain(e))},
                    {"body", export_expr(binding_body(e))}};
                break;
            case expr_kind::App:
                j["app"] = {export_expr(app_fn(e)), export_expr(app_arg(e))};
                break;
            case expr_kind::Let:
                j["let"] = {
                    {"name", json_of_name(let_name(e))},
                    {"type", export_expr(let_type(e))},
                    {"value", export_expr(let_value(e))},
                    {"body", export_expr(let_body(e))}};
                break;
        }
        auto r = m_exprs.size();
        m_exprs.push_back(std::move(j));
        m_expr2idx.emplace(e.raw(), r);
        return r;
    }

    void write_ast(std::ostream & out) {
        json asts = json::array({nullptr});
        for (unsigned i = 1; i < m_ast.size(); i++) {
            if (!m_reachable[i] || !m_ast[i]) {
                asts.push_back(nullptr);
                continue;
            }
            auto& data = *m_ast[i];
            lean_assert(data.m_type.is_atomic());
            json j {
                // {"id", data.m_id},
                {"kind", data.m_type.get_string()},
                {"start", {data.m_start.first, data.m_start.second}},
            };
            if (auto end = data.m_end) j["end"] = {end->first, end->second};
            if (data.m_value) {
                j["value"] = json_of_name(data.m_value);
            }
            if (!data.m_children.empty())
                j["children"] = data.m_children;
            if (data.m_pexpr) j["pexpr"] = export_expr(*data.m_pexpr);
            if (data.m_expr) {
                auto res = (*data.m_expr)->peek();
                j["expr"] = res ? export_expr(*res) : 0;
            }
            asts.push_back(j);
        }
        json r = {
            {"ast", asts},
            {"file", AST_TOP_ID},
            {"level", std::move(m_levels)},
            {"expr", std::move(m_exprs)},
        };
        if (m_tactic_log) {
            lean_assert(!m_tactic_log->m_detached);
            m_tactic_log->m_exported.store(true);
            lock_guard<mutex> l(m_tactic_log->m_mutex);
            auto& invocs = m_tactic_log->get_invocs(l);
            if (!invocs.empty()) {
                r["tactics"] = invocs;
                auto& ss = r["states"] = json::array();
                for (auto& s : m_tactic_log->get_states(l)) {
                    auto gs = json::array();
                    for (auto& g : s.goals()) {
                        auto hs = json::array();
                        for (auto& h : g.m_hyps) {
                            json j = {
                                {"name", json_of_name(h.m_name)},
                                {"pp", json_of_name(h.m_pp_name)},
                                {"type", export_expr(h.m_type)}
                            };
                            if (h.m_value) j["value"] = export_expr(*h.m_value);
                            hs.push_back(j);
                        }
                        gs.push_back({hs, export_expr(g.m_target_type)});
                    }
                    ss.push_back({{"decl", json_of_name(s.decl_name())}, {"goals", gs}});
                }
            }
        }
        out << r;
    }
};

std::string json_of_lean(std::string const & lean_fn) {
    if (lean_fn.size() > 5 && lean_fn.substr(lean_fn.size() - 5) == ".lean") {
        return lean_fn.substr(0, lean_fn.size() - 5) + ".ast.json";
    } else {
        throw exception(sstream() << "not a .lean file: " << lean_fn);
    }
}

void export_ast(parser const & p) {
    if (p.m_ast.empty() || p.m_ast_invalid) return;
    auto ast_fn = json_of_lean(p.m_file_name);
    std::cerr << "exporting " << ast_fn << std::endl;
    exclusive_file_lock output_lock(ast_fn);
    std::ofstream out(ast_fn);
    ast_exporter(p.m_ast, p.m_tag_ast_table, p.m_tactic_log.get()).write_ast(out);
    out.close();
    if (!out) throw exception(sstream() << "failed to write ast file: " << ast_fn);
}

#else
void export_ast(parser const &) {}
#endif // LEAN_JSON

}
