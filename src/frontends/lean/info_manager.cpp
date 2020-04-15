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
        record["full-id"] = m_full_id.to_string();
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

void render_attr(vm_obj const & attr, json & record, std::vector<ts_vm_obj> & handlers) {
    switch (cidx(attr)) {
        case 0: // val : string -> string -> attr
            record[to_string(cfield(attr, 0))] = to_string(cfield(attr, 1));
            break;
        case 1: // on_click
            record["onClick"] = handlers.size();
            handlers.push_back(cfield(attr, 0));
            break;
        case 2: { // style
            auto l = cfield(attr, 0);
            while (!is_simple(l)) {
                auto h = head(l);
                record["style"][to_string(cfield(h, 0))] = to_string(cfield(h, 1));
                l = tail(l);
            }
            break;}
    }
}

void render_html(vm_obj const & html, json & j_arr, std::vector<ts_vm_obj> & handlers) {
    switch (cidx(html)) {
        case 0: { // element : string -> list (attr) -> html -> html
            json entry;
            entry["tag"] = to_string(cfield(html, 0));
            vm_obj l = cfield(html, 1);
            while (!is_simple(l)) {
                render_attr(head(l), entry["attributes"], handlers);
                l = tail(l);
            }
            entry["children"] = json::array();
            render_html(cfield(html, 2), entry["children"], handlers);
            j_arr.push_back(entry);
            break; }
        case 1: // of_string : string -> html
            j_arr.push_back(to_string(cfield(html, 0)));
            break;
        case 2: // empty : html
            break;
        case 3: { // append : html -> html -> html
            render_html(cfield(html, 0), j_arr, handlers);
            render_html(cfield(html, 1), j_arr, handlers);
            break;
        }
    }
}
void widget_info::render(lean::vm_state & S) const {
    json view = json::array();
    std::vector<ts_vm_obj> handlers;
    render_html(S.invoke(cfield(m_widget.to_vm_obj(), 2), m_state.to_vm_obj()), view, handlers);
    const_cast<widget_info*>(this)->m_view = view;
    const_cast<widget_info*>(this)->m_event_handlers = handlers;
}

void widget_info::report(io_state_stream const & ios, json & record) const {
    if (!m_view) {
        vm_state S(m_env, ios.get_options());
        scope_vm_state scope(S);
        render(S);
    }
    record["widget"]["html"] = *m_view;
}

bool widget_info::update(io_state_stream const & ios, json const & message, json & record) const {
    unsigned handler_idx = message["handler"];
    json args = message["args"];
    vm_state S(m_env, ios.get_options());
    scope_vm_state scope(S);
    unsigned handler_size = 0;
    if (m_event_handlers) {
        handler_size = (*m_event_handlers).size();
    }
    if (handler_idx >= handler_size) {
        return false;
    }
    // [todo] figure out the form of event_args and pass them through to the vm handler.
    auto handler = ((*m_event_handlers)[handler_idx]).to_vm_obj();
    vm_obj update = S.invoke(cfield(m_widget.to_vm_obj(), 1), m_state.to_vm_obj(), S.invoke(handler, mk_vm_unit()));
    // [hack] morally, I should remove all the const qualifiers from widget info methods, since their content is _actually_
    // mutating. I found that doing this caused a cascading chain of having to remove the 'const' from many things so in
    // the name of preserving as much of the other lean source as possible I have opted to just add a const_cast here instead. e.w.ayers
    const_cast<widget_info*>(this)->m_state = cfield(update, 0);
    vm_obj action = cfield(update, 1); // [todo] use this to perform some external state change.
    render(S);
    record["status"] = "success"; // [todo] there is already a status indicator on the object above "record".
    record["widget"]["html"] = *m_view;
    return true;
}

info_data mk_type_info(expr const & e) { return info_data(new type_info_data(e)); }
info_data mk_identifier_info(name const & full_id) { return info_data(new identifier_info_data(full_id)); }
info_data mk_vm_obj_format_info(environment const & env, vm_obj const & thunk) {
    return info_data(new vm_obj_format_info(env, thunk));
}
info_data mk_widget_info(environment const & env, vm_obj const & widget) {
    vm_obj state =  cfield(widget, 0); // call widget.init to get the initial state.
    return info_data(new widget_info(env, state, widget));
}
info_data mk_hole_info(tactic_state const & s, expr const & hole_args, pos_info const & begin, pos_info end) {
    return info_data(new hole_info_data(s, hole_args, begin, end));
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

void info_manager::add_widget_info(pos_info pos, environment const & env, vm_obj const & widget) {
#ifdef LEAN_NO_INFO
    return;
#endif
    add_info(pos, mk_widget_info(env, widget));
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

bool info_manager::update_widget(environment const & env, options const & o, io_state const & ios, pos_info pos, json & record, json const & message) const {
    type_context_old tc(env, o);
    io_state_stream out = regular(env, ios, tc).update_options(o);
    auto ds = get_info(pos);
    if (!ds) {
        // record["status"] = "error";
        // record["message"] = "could not find a widget at the given position";
        return false;
     }
    for (auto & d : *ds) {
        const widget_info* cw = is_widget_info(d);
        widget_info * w = const_cast<widget_info*>(cw);
        if (w) {
            return w->update(out, message, record);
        }
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

vm_obj tactic_save_widget(vm_obj const & pos, vm_obj const & widget_fn, vm_obj const & s) {
    try {
        if (g_info_m) {
            g_info_m->add_widget_info(to_pos_info(pos), tactic::to_state(s).env(), invoke(widget_fn, s));
        }
        return tactic::mk_success(tactic::to_state(s));
    } catch (exception & ex) {
        return tactic::mk_exception(ex, tactic::to_state(s));
    }
}

void initialize_info_manager() {
    DECLARE_VM_BUILTIN(name({"tactic", "save_info_thunk"}),  tactic_save_info_thunk);
    DECLARE_VM_BUILTIN(name({"tactic", "save_widget"}),  tactic_save_widget);
}
void finalize_info_manager() {
}
}
