/*
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
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
#include "frontends/lean/widget_info.h"
#include "frontends/lean/interactive.h"
#include "util/task_builder.h"

namespace lean {

widget_info const * is_widget_info(info_data const & d) {
    return dynamic_cast<widget_info const *>(d.raw());
}

json widget_info::to_json() const {
    vdom * vd = const_cast<vdom*>(&m_vdom);
    return vd->to_json();
}

void widget_info::report(io_state_stream const & ios, json & record) const {
    if (!get_global_module_mgr()->get_report_widgets()) { return; }
    mutex * mp = const_cast<mutex *>(&m_mutex);
    lock_guard<mutex> _(*mp);
    vm_state S(m_env, ios.get_options());
    scope_vm_state scope(S);
    pending_tasks pts;
    set_pending_tasks(&pts);
    record["widget"]["html"] = to_json();
    unset_pending_tasks();
    any(pts, [] (list<unsigned> route) => {
        // perform the update. notify the server somehow, probably through the log tree.
    })
    // [todo] for each task in pts notify the logtree that the state changed whenever one of the tasks completes.

    // sketch: I would rather this does something like 'task.first_to_complete(gs)`
    for (auto pt:pts) {
        gtask g = pt.first;
        auto route = pt.second.first;
        auto handler_id = pt.second.second;
        taskq().submit(task_builder([g, route, handler_id] {
            auto r = g.get();
            auto res = c->handle_event(route, handler_id, mk_vm_unit());
            lean_assert(!res);
            return unit{};
        }).depends_on(g).build());
    }
}
/*
interface message {
    handler : {h: number; r: number[]};
    args:
        | { type : "string"; value : string}
        | { type : "unit"}
        | { type: "mouse_capture"};
}

type response =
| { widget?: {html: any};
    status: "success";}
| { status: "invalid_handler" | "error" }
| { status: "edit"; text: string; widget? }
 */
void widget_info::update(io_state_stream const & ios, json const & message, json & record) {
    if (!get_global_module_mgr()->get_report_widgets()) { return; }
    lock_guard<mutex> _(m_mutex);
    vm_state S(m_env, ios.get_options());
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
    } else if (arg_type == "mouse_capture") {
        try {
            c->handle_mouse_lose_capture(m_mouse_focus);
            c->handle_mouse_gain_capture(route);
            m_mouse_focus = route;
            record["status"] = "success";
            record["widget"]["html"] = to_json();
        } catch (const invalid_handler & e) {
            record["status"] = "invalid_handler";
        }
        return;
    } else {
        throw exception("expecting arg_type to be either 'unit' or 'string' but was '" + arg_type + "'");
    }
    try {
        optional<vm_obj> result = c->handle_event(route, handler_idx, vm_args);
        record["widget"]["html"] = to_json();
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

info_data mk_widget_info(environment const & env, vm_obj const & props, vm_obj const & widget) {
    vdom c = vdom(new component_instance(widget, props));
    return info_data(new widget_info(env, c));
}

bool info_manager::update_widget(environment const & env, options const & o, io_state const & ios, pos_info pos, json & record, json const & message) const {
    type_context_old tc(env, o);
    io_state_stream out = regular(env, ios, tc).update_options(o);
    auto ds = get_info(pos);
    if (!ds) {
        record["status"] = "error";
        record["message"] = "could not find a widget at the given position";
        return false;
     }
    for (auto & d : *ds) {
        const widget_info* cw = is_widget_info(d);
        widget_info * w = const_cast<widget_info*>(cw);
        if (w) {
            w->update(out, message, record);
            return true;
        }
    }
    return false;
}

void info_manager::add_widget_info(pos_info pos, vm_obj const & props, vm_obj const & widget) {
#ifdef LEAN_NO_INFO
    return;
#endif
    add_info(pos, mk_widget_info(tactic::to_state(props).env(), props, widget));
}


}
