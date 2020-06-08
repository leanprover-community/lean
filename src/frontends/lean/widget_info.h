/*
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
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
#include "frontends/lean/info_manager.h"

namespace lean {

class widget_info : public info_data_cell {
    environment  m_env;
    vdom         m_vdom;
    mutex        m_mutex;
    list<unsigned> m_mouse_focus;
    /** Event */
    // event<unit>   m_update_task;
public:
    widget_info(environment const & env, vdom const & vd): m_env(env), m_vdom(vd) {}
    virtual void report(io_state_stream const & ios, json & record) const override;
    /** Given a message of the form
     * `{handler: {h: number; r: number[]}, args: {type: "string" | "unit"; value} }`,
     * runs the event handler and updates the state.
     * The record is updated to have `{status : "success", widget : {html : _}}` on success.
     * If the widget update event yields an action then the record will be of type `{status: "edit", action: string, widget:_}`
     * If the handler given does not correspond to a component on the widget, then the record is set to `{status: "invalid_handler"}`.
     * It will throw is the json message has the wrong format.
     */
    void update(io_state_stream const & ios, json const & message, json & record);
    json to_json() const;
};

widget_info const * is_widget_info(info_data const & d);

}