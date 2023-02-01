/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <vector>
#include <string>
#include "kernel/expr.h"
#include "library/io_state_stream.h"
#include "library/metavar_context.h"
#include "library/vm/vm.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/json.h"
#include "frontends/lean/widget.h"

namespace lean {
class info_data;

class info_data_cell {
    MK_LEAN_RC();
    void dealloc() { delete this; }
protected:
    friend info_data;
public:
    info_data_cell():m_rc(0) {}
    virtual ~info_data_cell() {}
    virtual void instantiate_mvars(metavar_context const &) {}
#ifdef LEAN_JSON
    virtual void report(io_state_stream const & ios, json & record) const = 0;
#endif
};

class identifier_info_data : public info_data_cell {
    name m_full_id;
    bool m_is_const;
public:
    identifier_info_data(name const & full_id, bool is_const):
	m_full_id(full_id), m_is_const(is_const) {}
    name get_full_id() const { return m_full_id; };
    bool is_const() const { return m_is_const; };

#ifdef LEAN_JSON
    virtual void report(io_state_stream const & ios, json & record) const;
#endif
};

/** A format thunk, as is generated through `tactic.save_info_thunk : pos -> (unit -> format) -> tactic unit`.  */
class vm_obj_format_info : public info_data_cell {
    /** The environment of the tactic state at the moment that save_info_thunk was called */
    environment      m_env;
    /** The thunk provided from `save_info_thunk` */
    ts_vm_obj        m_thunk;
    /** A memoised format from the thunk */
    optional<format> m_cache;
public:
    vm_obj_format_info(environment const & env, vm_obj const & thunk): m_env(env), m_thunk(thunk) {}
#ifdef LEAN_JSON
    virtual void report(io_state_stream const & ios, json & record) const;
#endif
};

class hole_info_data : public info_data_cell {
    tactic_state m_state;
    expr         m_args;
    pos_info     m_begin_pos;
    pos_info     m_end_pos;
    /* TODO(Leo): we need to store the string for command containing the whole, and where it starts */
public:
    hole_info_data(tactic_state const & s, expr const & args, pos_info const & b, pos_info const & e):
        m_state(s), m_args(args), m_begin_pos(b), m_end_pos(e) {}

#ifdef LEAN_JSON
    virtual void report(io_state_stream const & ios, json & record) const override;
#endif
    tactic_state const & get_tactic_state() const { return m_state; }
    expr const & get_args() const { return m_args; }
    pos_info const & get_begin_pos() const { return m_begin_pos; }
    pos_info const & get_end_pos() const { return m_end_pos; }
};

class widget_info : public info_data_cell {
protected:
    environment  m_env;
    pos_info     m_pos;
    unsigned     m_id = 0;
    vdom         m_vdom;
    mutex        m_mutex;
    widget_info(environment const & env, pos_info const & pos) : m_env(env), m_pos(pos) {}
public:
    widget_info(environment const & env, pos_info const & pos, unsigned id, vdom const & vd): m_env(env), m_pos(pos), m_id(id), m_vdom(vd) {}
    void get(json & record);
    /** Given a message of the form
     * `{handler: {h: number; r: number[]}, args: {type: "string" | "unit"; value} }`,
     * runs the event handler and updates the state.
     * The record is updated to have `{status : "success", widget : {html : _}}` on success.
     * If the widget update event yields an action then the record will be of type `{status: "edit", action: string, widget:_}`
     * If the handler given does not correspond to a component on the widget, then the record is set to `{status: "invalid_handler"}`.
     * It will throw is the json message has the wrong format.
     */
    void update(json const & message, json & record);
    json to_json() const;
    virtual void report(io_state_stream const &, json &) const {}

    bool has_widget() const { return m_vdom.raw(); }
    unsigned id() const { return m_id; }
};

class widget_goal_info : public widget_info {
public:
    widget_goal_info(environment const & env, pos_info const & pos, unsigned id, vdom const & vd) :
        widget_info(env, pos, id, vd) {}
    virtual void report(io_state_stream const & ios, json & record) const override;
};

class info_data {
private:
    info_data_cell * m_ptr;
public:
    info_data(info_data_cell * c):m_ptr(c) { lean_assert(c); m_ptr->inc_ref(); }
    info_data(info_data const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    info_data(info_data && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~info_data() { if (m_ptr) m_ptr->dec_ref(); }
    friend void swap(info_data & a, info_data & b) { std::swap(a.m_ptr, b.m_ptr); }
    info_data & operator=(info_data const & s) { LEAN_COPY_REF(s); }
    info_data & operator=(info_data && s) { LEAN_MOVE_REF(s); }
    info_data_cell const * raw() const { return m_ptr; }
#ifdef LEAN_JSON
    void report(io_state_stream const & ios, json & record) const {
        return m_ptr->report(ios, record);
    }
#endif
    void instantiate_mvars(metavar_context const & mctx) const {
        m_ptr->instantiate_mvars(mctx);
    }
};

hole_info_data const * is_hole_info_data(info_data const & d);
hole_info_data const & to_hole_info_data(info_data const & d);
vm_obj_format_info const * is_vm_obj_format_info(info_data const & d);
widget_info const * is_widget_info(info_data const & d);
widget_goal_info const * is_widget_goal_info(info_data const & d);
bool is_term_goal(info_data const & d);

optional<std::string> get_doc_string_including_override(environment const & env, name const & n);

typedef rb_map<unsigned, list<info_data>, unsigned_cmp> line_info_data_set;

class info_manager : public log_entry_cell {
    std::string m_file_name;
    rb_map<unsigned, line_info_data_set, unsigned_cmp> m_line_data;

public:
    void add_info(pos_info pos, info_data data);
    info_manager() {}
    info_manager(std::string const & file_name) : m_file_name(file_name) {}

    std::string get_file_name() const { return m_file_name; }

    bool empty() const { return m_line_data.empty(); }

    void add_type_info(pos_info pos, expr const & e);
    void add_identifier_info(pos_info pos, name const & full_id, bool is_const);
    /* Takes type info from global declaration with the given name. */
    void add_const_info(environment const & env, pos_info pos, name const & full_id);
    void add_vm_obj_format_info(pos_info pos, environment const & env, vm_obj const & thunk);
    void add_widget_info(pos_info pos, vm_obj const & ts, vm_obj const & widget);
    void add_widget_goal_info(pos_info pos, vm_obj const & ts, vm_obj const & widget);
    void add_hole_info(pos_info const & begin_pos, pos_info const & end_pos, tactic_state const & s, expr const & hole_args);
    void add_term_goal(pos_info const & pos, tactic_state const & s);

    line_info_data_set get_line_info_set(unsigned l) const;
    rb_map<unsigned, line_info_data_set, unsigned_cmp> const & get_line_info_sets() const { return m_line_data; }

    void instantiate_mvars(metavar_context const & mctx);
    void merge(info_manager const & info);

#ifdef LEAN_JSON
    void get_info_record(environment const & env, options const & o, io_state const & ios, pos_info pos,
                         json & record, std::function<bool (info_data const &)> pred = {}) const;
#endif
    optional<list<info_data>> get_info(pos_info pos) const;
    /** Mutate the widget's state according to the widget's VM update function, expecting message to have the type;
     *  Returns true when the widget was successfully updated.
     */
    bool update_widget(pos_info pos, unsigned id, json & record, json const & message) const;
    bool get_widget(pos_info pos, unsigned id, json & record) const;
};

info_manager * get_global_info_manager();
class scoped_info_manager {
    info_manager * m_old;
public:
    scoped_info_manager(info_manager * infom);
    ~scoped_info_manager();
};

class auto_reporting_info_manager_scope {
    std::shared_ptr<info_manager> m_infom;
    scoped_info_manager m_infom_scope;

public:
    auto_reporting_info_manager_scope(std::string const & file_name, bool enabled) :
            m_infom(enabled ? std::make_shared<info_manager>(file_name) : nullptr),
            m_infom_scope(enabled ? &*m_infom : nullptr) {}

    ~auto_reporting_info_manager_scope() {
        if (m_infom && !m_infom->empty()) {
            try {
                logtree().add(m_infom);
            } catch (...) {}
        }
    }
};

void initialize_info_manager();
void finalize_info_manager();
}
