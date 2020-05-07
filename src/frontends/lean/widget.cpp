/*
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
*/
#include <map>
#include <vector>
#include <string>
#include "library/vm/vm.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_list.h"
#include "util/list.h"
#include "frontends/lean/widget.h"
#include "frontends/lean/json.h"
#include "util/optional.h"
#include "util/pair.h"

namespace lean {

optional<std::string> vdom_element::key() {
    if (m_attrs.find("key") != m_attrs.end()) {
        // there is an entry with key "key"
        std::string k = m_attrs["key"];
        return optional<std::string>(k);
    }
    return optional<std::string>();
}
void vdom_element::reconcile(vdom const & old_vdom) {
    vdom_element * o = dynamic_cast<vdom_element*>(old_vdom.raw());
    if (o && o->m_tag == m_tag) {
        std::vector<vdom> ocs = o->m_children;
        reconcile_children(m_children, ocs);
        if (m_tooltip && o->m_tooltip) {
            (*m_tooltip).reconcile(*(o->m_tooltip));
        }
    }
}
json vdom_element::to_json(list<unsigned> const & route) {
    json entry;
    entry["tag"] = m_tag;
    entry["attributes"] = m_attrs;
    json jr = json::array();
    for (auto const & i : route) {
        jr.push_back(i);
    }
    for (auto const & x : m_events) {
        entry["events"][x.first]["route"] = jr;
        entry["events"][x.first]["handler"] = json(x.second);
    }
    entry["children"] = json::array();
    for (vdom & v : m_children) {
        entry["children"].push_back(v.to_json(route));
    }
    if (m_tooltip) {
        entry["tooltip"] = (*m_tooltip).to_json(route);
    }
    return entry;
}

vm_obj component_instance::init(vm_obj const & p, optional<vm_obj> const & s) {
    vm_obj os = s ? mk_vm_some(*s) : mk_vm_none();
    return invoke(cfield(m_component.to_vm_obj(), 0), p, os);
}

pair<vm_obj, optional<vm_obj>> component_instance::update(vm_obj const & p, vm_obj const & s, vm_obj const & a) {
    vm_obj sa = invoke(cfield(m_component.to_vm_obj(), 1), p, s, a);
    vm_obj oa = cfield(sa, 1);
    optional<vm_obj> o = is_none(oa) ? optional<vm_obj>() : optional<vm_obj>(get_some_value(oa));
    return mk_pair(cfield(sa, 0), o);
}

vm_obj component_instance::view(vm_obj const & p, vm_obj const & s) {
    return invoke(cfield(m_component.to_vm_obj(), 2), p, s);
}

void component_instance::render() {
    std::vector<component_instance *> children;
    std::map<unsigned, ts_vm_obj> handlers;
    std::vector<vdom> elements = render_html_list(view(m_props.to_vm_obj(), (*m_state).to_vm_obj()), children, handlers, cons(m_id, m_route));
    std::vector<vdom> old_elements = m_render;
    reconcile_children(elements, old_elements);
    m_handlers = handlers;
    m_children = children;
    m_render = elements;
    m_has_rendered = true;
}

void component_instance::reconcile(vdom const & old) {
    lean_assert(!m_has_rendered);
    component_instance * ci_old = dynamic_cast<component_instance *>(old.raw());
    if (ci_old->m_component.to_vm_obj().raw() == m_component.to_vm_obj().raw()) { // [todo] check this works
        // copy over the state from our previous version.
        if (m_props.to_vm_obj() == ci_old->m_props.to_vm_obj()) { // [todo] use dec-eq here
            m_handlers = ci_old->m_handlers;
            m_children = ci_old->m_children;
            m_render   = ci_old->m_render;
            m_state    = ci_old->m_state;
            m_id       = ci_old->m_id;
            m_has_rendered = true;
            lean_assert(m_route == ci_old->m_route);
        } else {
            optional<vm_obj> old_state = some((*(ci_old->m_state)).to_vm_obj());
            ts_vm_obj new_state = init(m_props.to_vm_obj(), old_state);
            m_state = optional<ts_vm_obj>(new_state);
            render();
        }
    } else {
        m_state = some<ts_vm_obj>(init(m_props.to_vm_obj(), optional<vm_obj>()));
        render();
    }
}

json component_instance::to_json(list<unsigned> const & route) {
    if (!m_has_rendered) {
        if (!m_state) {
            m_state = some<ts_vm_obj>(init(m_props.to_vm_obj(), optional<vm_obj>()));
        }
        render();
    }
    json result = json::array();
    for (vdom const & x : m_render) {
        result.push_back(x.to_json(cons(m_id, route)));
    }
    return result;
}

optional<vm_obj> component_instance::handle_action(vm_obj const & a) {
    auto p = update(m_props.to_vm_obj(), (*m_state).to_vm_obj(), a);
    m_state = p.first;
    render();
    return p.second;
}

optional<vm_obj> component_instance::handle_event(list<unsigned> const & route, unsigned handler_id, vm_obj const & event_args) {
    if (empty(route)) {
        if (m_handlers.find(handler_id) == m_handlers.end()) {
            // component may have rerendered, but handler_id refers to event handler on older component.
            throw invalid_handler();
        }
        ts_vm_obj handler = m_handlers[handler_id];
        // [todo] to prevent a VM error in the case of bad client code, we should check that the 'type' of the event_args here is the same as what the handler expects.
        // the event record from the client should have a `type` member which can be checked. So each of `m_handlers` should also include a string 'type' to check against.
        auto action = invoke(handler.to_vm_obj(), event_args);
        return handle_action(action);
    }
    for (auto const & c : m_children) {
        if (c->m_id == head(route)) {
            optional<vm_obj> a = c->handle_event(tail(route), handler_id, event_args);
            if (a) {
                return handle_action(*a);
            } else {
                return optional<vm_obj>();
            }
        }
    }
    // given component no longer exists. This happens if the ui is updated but there are events from an old
    throw invalid_handler();
}

void reconcile_children(std::vector<vdom> & new_elements, std::vector<vdom> const & olds) {
    std::vector<vdom> old_elements = olds;
    for (unsigned i = 0; i < new_elements.size(); i++) {
        // [note] you get wierd behaviour if multiple things have the same key or if only some elements have keys
        // but this is also true in React so I am not too worried about it as long as it doesn't crash.
        // [note] could probably avoid a few vdom copies but w/e
        auto k = new_elements[i].key();
        if (k) {
            for (unsigned j = 0; j < old_elements.size(); j++) {
                if (old_elements[j].key() == k) {
                    vdom o = old_elements[j];
                    new_elements[i].reconcile(o);
                    old_elements.erase(old_elements.begin() + j);
                    break;
                }
            }
        } else if (old_elements.size() > 0) {
            new_elements[i].reconcile(old_elements[0]);
            old_elements.erase(old_elements.begin());
        } else {
            // continue
        }
    }
}

void render_event(std::string const & name, vm_obj const & handler, std::map<std::string, unsigned> & events, std::map<unsigned, ts_vm_obj> & handlers) {
    static unsigned handler_count = 0; // [fixme] threading issues here;
    unsigned handler_id = handler_count++;

    events[name] = handler_id;
    handlers[handler_id] = handler;
}

vdom render_element(vm_obj const & elt, std::vector<component_instance*> & components, std::map<unsigned, ts_vm_obj> & handlers, list<unsigned> const & route) {
    std::string tag = to_string(cfield(elt, 0));
    vm_obj v_attrs = cfield(elt, 1);
    json attributes;
    std::map<std::string, unsigned> events;
    optional<vdom> tooltip;
    while (!is_simple(v_attrs)) {
        vm_obj attr = head(v_attrs);
        v_attrs = tail(v_attrs);
        switch (cidx(attr)) {
            case 0: { // val : string -> string -> attr
                std::string key = to_string(cfield(attr, 0));
                std::string value = to_string(cfield(attr, 1));
                if (key == "className" && attributes.find(key) != attributes.end()) { // [hack] className fields should be merged. Should really be handled in lean.
                    std::string cn = attributes[key];
                    cn += " ";
                    cn += value;
                    attributes[key] = cn;
                } else {
                    attributes[key] = value;
                }
                break;
            }
            case 1: {// on_mouse_event : mouse_event_kind -> (unit -> Action) -> html.attr
                switch (cidx(cfield(attr, 0))) {
                    case 0: render_event("onClick",      cfield(attr, 1), events, handlers); break;
                    case 1: render_event("onMouseEnter", cfield(attr, 1), events, handlers); break;
                    case 2: render_event("onMouseLeave", cfield(attr, 1), events, handlers); break;
                    default: lean_unreachable();
                }
                break;
            }
            case 2: { // style : list (string × string) → html.attr
                auto l = cfield(attr, 0);
                while (!is_simple(l)) {
                    auto h = head(l);
                    attributes["style"][to_string(cfield(h, 0))] = to_string(cfield(h, 1));
                    l = tail(l);
                }
                break;
            }
            case 3: { // tooltip : html Action → html.attr
                vdom tooltip_child = render_html(cfield(attr, 0), components, handlers, route);
                tooltip = optional<vdom>(tooltip_child);
                break;
            }
            case 4: { // text_change_event : (string -> Action) -> html.attr
                render_event("onChange", cfield(attr, 0), events, handlers);
                break;
            }
            default : {
                lean_unreachable();
                break;
            }
        }
    }
    std::vector<vdom> children = render_html_list(cfield(elt, 2), components, handlers, route);
    return vdom(new vdom_element(tag, attributes, events, children, tooltip));
}

vdom render_html(vm_obj const & html, std::vector<component_instance*> & components, std::map<unsigned, ts_vm_obj> & handlers, list<unsigned> const & route) {
    switch (cidx(html)) {
        case 0: { // of_element : element -> html
            vdom elt = render_element(cfield(html, 0), components, handlers, route);
            return elt;
        }
        case 1: { // of_string : string -> html
            return vdom(new vdom_string(to_string(cfield(html, 0))));
        }
        case 2: { // of_component : {π : Type}: π → component π α → html
            vm_obj props = cfield(html, 0);
            vm_obj comp = cfield(html, 1);
            component_instance * c = new component_instance(comp, props, route);
            components.push_back(c);
            return vdom(c);
        }
        default: {
            lean_unreachable();
        }
    }
}

std::vector<vdom> render_html_list(vm_obj const & htmls, std::vector<component_instance*> & components, std::map<unsigned, ts_vm_obj> & handlers, list<unsigned> const & route) {
    std::vector<vdom> elements;
    vm_obj l = htmls;
    while (!is_simple(l)) {
        vdom x = render_html(head(l), components, handlers, route);
        elements.push_back(x);
        l = tail(l);
    }
    return elements;
}

// class vm_vdom : public vm_external {
//     vdom m_val;
//     vm_vdom(vdom const & v) : m_val(v) {}
//     virtual ~vm_vdom() {}
//     virtual void dealloc() { this->~vm_vdom(); get_vm_allocator().deallocate(sizeof(vm_vdom), this); }
//     virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_vdom(m_val); }
//     virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_vdom))) vm_vdom(m_val); }
// }

// vm_obj to_obj(vdom const & v) {
//     return mk_vm_external(new(get_vm_allocator().allocate(sizeof(vm_vdom))) vm_vdom(v));
// }

// vdom to_vdom(vm_obj const & o) {
//     lean_vm_check(dynamic_cast<vm_vdom*>(to_external(o)));
//     return static_cast<vm_vdom*>(to_external(o))->m_val;
// }

vm_obj vm_of_element(vm_obj const &, vm_obj const & e) {
    return mk_vm_constructor(0, e);
}

vm_obj vm_of_string(vm_obj const &, vm_obj const & o) {
    return mk_vm_constructor(1, o);
}

vm_obj vm_of_component(vm_obj const &, vm_obj const &, vm_obj const & vprops, vm_obj const & vcomp) {
    return mk_vm_constructor(2, vprops, vcomp);
}

vm_obj vm_html_cases(vm_obj const &, vm_obj const &, vm_obj const & fe, vm_obj const & fs, vm_obj const & fc, vm_obj const & html) {
    switch (cidx(html)) {
        case 0: return invoke(fe, cfield(html, 0));
        case 1: return invoke(fs, cfield(html, 0));
        case 2: return invoke(fc, mk_vm_simple(0), cfield(html, 0), cfield(html, 1));
        default: lean_unreachable();
    }
}

vm_obj vm_component_mk(
    vm_obj const &, vm_obj const &,
    vm_obj const &, vm_obj const &,
    vm_obj const & i,
    vm_obj const & u,
    vm_obj const & v) {
    return mk_vm_constructor(0, i, u, v);
    }

void initialize_widget() {
    DECLARE_VM_BUILTIN(name({"html", "of_element"}), vm_of_element);
    DECLARE_VM_BUILTIN(name({"html", "of_string"}),  vm_of_string);
    DECLARE_VM_BUILTIN(name({"html", "of_component"}), vm_of_component);
    DECLARE_VM_BUILTIN(name({"html", "cases"}),  vm_html_cases);

    DECLARE_VM_BUILTIN(name({"component", "mk"}), vm_component_mk);
    DECLARE_VM_BUILTIN(name({"component", "state"}),   [](vm_obj const &, vm_obj const &) { return mk_vm_simple(0); });
    DECLARE_VM_BUILTIN(name({"component", "event"}),   [](vm_obj const &, vm_obj const &) { return mk_vm_simple(0); });
    DECLARE_VM_BUILTIN(name({"component", "init"}),    [](vm_obj const &, vm_obj const &, vm_obj const & c) { return cfield(c, 0); });
    DECLARE_VM_BUILTIN(name({"component", "update"}),  [](vm_obj const &, vm_obj const &, vm_obj const & c) { return cfield(c, 1); });
    DECLARE_VM_BUILTIN(name({"component", "view"}),    [](vm_obj const &, vm_obj const &, vm_obj const & c) { return cfield(c, 2); });
}

void finalize_widget() {}

}
