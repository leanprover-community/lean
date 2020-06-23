/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <vector>
#include <set>
#include <string>
#include "kernel/type_checker.h"
#include "library/trace.h"
#include "library/documentation.h"
#include "library/scoped_ext.h"
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_pos_info.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/json.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/interactive.h"
#include "library/constants.h"

namespace lean {
class type_info_data : public info_data_cell {
protected:
    expr m_expr;
public:
    type_info_data(expr const & e): m_expr(e) {}

    expr const & get_type() const { return m_expr; }

    virtual void instantiate_mvars(metavar_context const & mctx) override {
        m_expr = metavar_context(mctx).instantiate_mvars(m_expr);
    }

#ifdef LEAN_JSON
    virtual void report(io_state_stream const & ios, json & record) const override {
        interactive_report_type(ios.get_environment(), ios.get_options(), m_expr, record);
    }
#endif
};

class identifier_info_data : public info_data_cell {
    name m_full_id;
public:
    identifier_info_data(name const & full_id): m_full_id(full_id) {}

#ifdef LEAN_JSON
    virtual void report(io_state_stream const & ios, json & record) const override {
        record["full-id"] = m_full_id.escape();
        add_source_info(ios.get_environment(), m_full_id, record);
        if (auto doc = get_doc_string(ios.get_environment(), m_full_id))
            record["doc"] = *doc;
    }
#endif
};

#ifdef LEAN_JSON
void hole_info_data::report(io_state_stream const & ios, json & record) const {
    type_context_old ctx = mk_type_context_for(m_state);
    interactive_report_type(ios.get_environment(), ios.get_options(), ctx.infer(m_state.main()), record);
}
#endif

hole_info_data const * is_hole_info_data(info_data const & d) {
    return dynamic_cast<hole_info_data const *>(d.raw());
}

hole_info_data const & to_hole_info_data(info_data const & d) {
    lean_assert(is_hole_info_data(d));
    return *static_cast<hole_info_data const *>(d.raw());
}
vm_obj_format_info const * is_vm_obj_format_info(info_data const & d) {
    return dynamic_cast<vm_obj_format_info const *>(d.raw());
}
widget_info const * is_widget_info(info_data const & d) {
    return dynamic_cast<widget_info const *>(d.raw());
}
widget_goal_info const * is_widget_goal_info(info_data const & d) {
    return dynamic_cast<widget_goal_info const *>(d.raw());
}


class term_goal_data : public widget_info {
    tactic_state m_state;

public:
    term_goal_data(tactic_state const & s, pos_info const & pos) : widget_info(s.env(), pos), m_state(s) {}

    virtual void instantiate_mvars(metavar_context const & mctx0) override {
        auto goal = m_state.get_main_goal_decl();
        if (!goal) return;
        auto mctx = mctx0;
        expr new_goal = mctx.mk_metavar_decl(goal->get_context(), goal->get_type());
        m_state = set_mctx_goals(m_state, mctx, list<expr>(new_goal));

        if (!get_global_module_mgr()->get_report_widgets()) { return; }
        if (m_env.find(get_widget_term_goal_widget_name())) try {
            vm_state S(m_env, options());
            vm_obj widget = S.get_constant(get_widget_term_goal_widget_name());
            auto ci = new component_instance(widget, to_obj(m_state));
            m_id = ci->id();
            m_vdom = vdom(ci);
        } catch (exception &) {}
    }

    virtual void report(io_state_stream const &, json & record) const override {
        record["state"] = (sstream() << m_state.pp()).str();
        if (!m_vdom.raw()) return;
        record["widget"]["line"] = m_pos.first;
        record["widget"]["column"] = m_pos.second;
        record["widget"]["id"] = m_id;
    }

    tactic_state const & get_tactic_state() const { return m_state; }
};

bool is_term_goal(info_data const & d) {
    return dynamic_cast<term_goal_data const *>(d.raw());
}

#ifdef LEAN_JSON
void vm_obj_format_info::report(io_state_stream const & ios, json & record) const {
    if (!m_cache) {
        vm_state S(m_env, ios.get_options());
        scope_vm_state scope(S);
        vm_obj thunk = m_thunk.to_vm_obj();
        const_cast<vm_obj_format_info*>(this)->m_cache = to_format(S.invoke(thunk, mk_vm_unit()));
    }
    std::ostringstream ss;
    ss << mk_pair(*m_cache, ios.get_options());
    record["state"] = ss.str();
}
#endif

json widget_info::to_json() const {
    vdom * vd = const_cast<vdom*>(&m_vdom);
    return vd->to_json();
}

void widget_goal_info::report(io_state_stream const &, json & record) const {
    if (!m_vdom.raw()) return;
    if (!get_global_module_mgr()->get_report_widgets()) { return; }
    record["widget"]["line"] = m_pos.first;
    record["widget"]["column"] = m_pos.second;
    record["widget"]["id"] = m_id;
}

void widget_info::get(json & record) {
    if (!m_vdom.raw()) return;
    if (!get_global_module_mgr()->get_report_widgets()) { return; }
    lock_guard<mutex> _(m_mutex);
    vm_state S(m_env, options());
    scope_vm_state scope(S);
    record["widget"]["html"] = to_json();
    record["widget"]["line"] = m_pos.first;
    record["widget"]["column"] = m_pos.second;
    record["widget"]["id"] = m_id;
}

void widget_info::update(json const & message, json & record) {
    if (!m_vdom.raw()) return;
    if (!get_global_module_mgr()->get_report_widgets()) { return; }
    lock_guard<mutex> _(m_mutex);
    vm_state S(m_env, options());
    scope_vm_state scope(S);
    unsigned handler_idx = message["handler"]["h"];
    json j_route = message["handler"]["r"]; // an array with the root index at the _back_.
    list<unsigned> route; // now root index is at the _front_.
    for (json::iterator it = j_route.begin(); it != j_route.end(); ++it) {
      route = cons(unsigned(*it), route);
    }
    route = tail(route); // disregard the top component id because that is the root component
    json j_args = message["args"];
    component_instance * c = const_cast<component_instance *>(dynamic_cast<component_instance *>(m_vdom.raw()));
    vm_obj vm_args;
    std::string arg_type = j_args["type"];
    if (arg_type == "unit") {
        vm_args = mk_vm_unit();
    } else if (arg_type == "string") {
          std::string arg = j_args["value"];
          vm_args = to_obj(arg);
    } else {
        throw exception("expecting arg_type to be either 'unit' or 'string' but was '" + arg_type + "'");
    }
    try {
        optional<vm_obj> result = c->handle_event(route, handler_idx, vm_args);
        record["widget"]["html"] = to_json();
        record["widget"]["line"] = m_pos.first;
        record["widget"]["column"] = m_pos.second;
        record["widget"]["id"] = m_id;
        if (result) {
            record["status"] = "edit";
            record["action"] = to_string(*result);
        } else {
            record["status"] = "success";
        }
    } catch (const invalid_handler & e) {
        record["status"] = "invalid_handler";
    }
}

info_data mk_type_info(expr const & e) { return info_data(new type_info_data(e)); }

info_data mk_identifier_info(name const & full_id) { return info_data(new identifier_info_data(full_id)); }

info_data mk_vm_obj_format_info(environment const & env, vm_obj const & thunk) {
    return info_data(new vm_obj_format_info(env, thunk));
}

info_data mk_widget_goal_info(environment const & env, pos_info const & pos, vm_obj const & props, vm_obj const & widget) {
    auto ci = new component_instance(widget, props);
    vdom c = ci;
    return info_data(new widget_goal_info(env, pos, ci->id(), c));
}

info_data mk_widget_info(environment const & env, pos_info const & pos, vm_obj const & props, vm_obj const & widget) {
    auto ci = new component_instance(widget, props);
    vdom c = ci;
    return info_data(new widget_goal_info(env, pos, ci->id(), c));
}

info_data mk_hole_info(tactic_state const & s, expr const & hole_args, pos_info const & begin, pos_info end) {
    return info_data(new hole_info_data(s, hole_args, begin, end));
}
info_data mk_term_goal(pos_info const & pos, tactic_state const & s) {
    return info_data(new term_goal_data(s, pos));
}

void info_manager::add_info(pos_info pos, info_data data) {
#ifdef LEAN_NO_INFO
    return;
#endif
    line_info_data_set line_set = m_line_data[pos.first];
    line_set.insert(pos.second, cons<info_data>(data, line_set[pos.second]));
    m_line_data.insert(pos.first, line_set);
}

line_info_data_set info_manager::get_line_info_set(unsigned l) const {
    if (auto it = m_line_data.find(l))
        return *it;
    return {};
}

void info_manager::instantiate_mvars(metavar_context const & mctx) {
    m_line_data.for_each([&](unsigned, line_info_data_set const & set) {
            set.for_each([&](unsigned, list<info_data> const & data) {
                    for (info_data const & info : data)
                        info.instantiate_mvars(mctx);
                });
        });
}

void info_manager::merge(info_manager const & info) {
#ifdef LEAN_NO_INFO
    return;
#endif
    info.m_line_data.for_each([&](unsigned line, line_info_data_set const & set) {
            set.for_each([&](unsigned col, list<info_data> const & data) {
                    buffer<info_data> b;
                    to_buffer(data, b);
                    unsigned i = b.size();
                    while (i > 0) {
                        --i;
                        add_info({line, col}, b[i]);
                    }
                });
        });
}

void info_manager::add_type_info(pos_info pos, expr const & e) {
#ifdef LEAN_NO_INFO
    return;
#endif
    add_info(pos, mk_type_info(e));
}

void info_manager::add_identifier_info(pos_info pos, name const & full_id) {
#ifdef LEAN_NO_INFO
    return;
#endif
    add_info(pos, mk_identifier_info(full_id));
}

void info_manager::add_const_info(environment const & env, pos_info pos, name const & full_id) {
    add_identifier_info(pos, full_id);
    add_type_info(pos, env.get(full_id).get_type());
}

void info_manager::add_hole_info(pos_info const & begin_pos, pos_info const & end_pos, tactic_state const & s, expr const & hole_args) {
#ifdef LEAN_NO_INFO
    return;
#endif
    info_data d = mk_hole_info(s, hole_args, begin_pos, end_pos);
    add_info(begin_pos, d);
}

void info_manager::add_vm_obj_format_info(pos_info pos, environment const & env, vm_obj const & thunk) {
#ifdef LEAN_NO_INFO
    return;
#endif
    add_info(pos, mk_vm_obj_format_info(env, thunk));
}

void info_manager::add_term_goal(pos_info const & pos, tactic_state const & s) {
#ifdef LEAN_NO_INFO
    return;
#endif
    add_info(pos, mk_term_goal(pos, s));
}

void info_manager::add_widget_info(pos_info pos, vm_obj const & props, vm_obj const & widget) {
#ifdef LEAN_NO_INFO
    return;
#endif
    add_info(pos, mk_widget_info(tactic::to_state(props).env(), pos, props, widget));
}

void info_manager::add_widget_goal_info(pos_info pos, vm_obj const & props, vm_obj const & widget) {
#ifdef LEAN_NO_INFO
    return;
#endif
    add_info(pos, mk_widget_goal_info(tactic::to_state(props).env(), pos, props, widget));
}


#ifdef LEAN_JSON
void info_manager::get_info_record(environment const & env, options const & o, io_state const & ios, pos_info pos,
                                   json & record, std::function<bool (info_data const &)> pred) const {
    type_context_old tc(env, o);
    io_state_stream out = regular(env, ios, tc).update_options(o);
    auto ds = get_info(pos);
    if (!ds) {return;}
    for (auto const & d : *ds) {
        if (!pred || pred(d)) {
            d.report(out, record);
        }
    }
}
#endif
optional<list<info_data>> info_manager::get_info(pos_info pos) const{
    auto ds = get_line_info_set(pos.first).find(pos.second);
    optional<list<info_data>> result;
    if (ds) { result = some(*ds); }
    return result;
}

bool info_manager::update_widget(pos_info pos, unsigned id, json & record, json const & message) const {
    auto ds = get_info(pos);
    if (!ds) return false;
    widget_info * w = nullptr;
    for (auto & d : *ds) {
        if (auto cw = is_widget_info(d)) {
            if (cw->has_widget() && cw->id() == id) {
                w = const_cast<widget_info *>(cw);
                break;
            }
        }
    }
    if (w) {
        w->update(message, record);
        return true;
    }
    return false;
}

bool info_manager::get_widget(pos_info pos, unsigned id, json & record) const {
    auto ds = get_info(pos);
    if (!ds) return false;
    widget_info * w = nullptr;
    for (info_data const & d : *ds) {
        if (auto cw = is_widget_info(d)) {
            if (cw->has_widget() && cw->id() == id) {
                w = const_cast<widget_info *>(cw);
                break;
            }
        }
    }
    if (w) {
        w->get(record);
        return true;
    }
    return false;
}

LEAN_THREAD_PTR(info_manager, g_info_m);
scoped_info_manager::scoped_info_manager(info_manager *infom) {
    m_old = g_info_m;
    g_info_m = infom;
}
scoped_info_manager::~scoped_info_manager() {
    g_info_m = m_old;
}
info_manager * get_global_info_manager() {
    return g_info_m;
}

vm_obj tactic_save_info_thunk(vm_obj const & pos, vm_obj const & thunk, vm_obj const & s) {
    try {
        if (g_info_m) {
            auto _pos = to_pos_info(pos);
            g_info_m->add_vm_obj_format_info(_pos, tactic::to_state(s).env(), thunk);
        }
        return tactic::mk_success(tactic::to_state(s));
    } catch (exception & ex) {
        return tactic::mk_exception(ex, tactic::to_state(s));
    }
}

vm_obj tactic_save_widget(vm_obj const & pos, vm_obj const & widget, vm_obj const & s) {
    try {
        if (g_info_m) {
            g_info_m->add_widget_goal_info(to_pos_info(pos), s, widget);
        }
        return tactic::mk_success(tactic::to_state(s));
    } catch (exception & ex) {
        return tactic::mk_exception(ex, tactic::to_state(s));
    }
}

vm_obj tactic_trace_widget_at(vm_obj const & _pos, vm_obj const & widget, vm_obj const & _text, vm_obj const & s) {
    try {
#ifndef LEAN_NO_INFO
        if (g_info_m && get_global_module_mgr()->get_report_widgets()) {
            auto pos = to_pos_info(_pos);
            auto wi = mk_widget_info(tactic::to_state(s).env(), pos, s, widget);
            auto & loc = logtree().get_location();
            g_info_m->add_info(pos, wi);
            logtree().add(std::make_shared<message>(loc.m_file_name, pos, to_string(_text), is_widget_info(wi)->id()));
        }
#endif
        return tactic::mk_success(tactic::to_state(s));
    } catch (exception & ex) {
        return tactic::mk_exception(ex, tactic::to_state(s));
    }
}

void initialize_info_manager() {
    DECLARE_VM_BUILTIN(name({"tactic", "save_info_thunk"}),  tactic_save_info_thunk);
    DECLARE_VM_BUILTIN(name({"tactic", "save_widget"}),  tactic_save_widget);
    DECLARE_VM_BUILTIN(name({"tactic", "trace_widget_at"}),  tactic_trace_widget_at);
}
void finalize_info_manager() {
}
}
