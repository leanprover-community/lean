/*
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
*/
#include <map>
#include <vector>
#include <string>
#include <atomic>
#include "library/vm/vm.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_pos_info.h"
#include "util/list.h"
#include "frontends/lean/widget.h"
#include "frontends/lean/json.h"
#include "util/optional.h"
#include "util/pair.h"

namespace lean {


// derived from library/init/meta/widget/basic.lean
enum component_idx {
    pure = 0,
    filter_map_action = 1,
    map_props = 2,
    with_should_update = 3,
    with_state = 4,
    with_effects = 5,
    // with_mouse
    // with_task
};
enum html_idx {
    element = 6,
    of_string = 7,
    of_component = 8
};
enum attr_idx {
    val = 9,
    mouse_event = 10,
    style = 11,
    tooltip = 12,
    text_change_event = 13
};
enum effect_idx {
    insert_text = 0,
    reveal_position = 1,
    highlight_position = 2,
    clear_highlighting = 3,
    copy_text = 4,
    custom = 5
};

std::atomic_uint g_fresh_component_instance_id;

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

json route_to_json(list<unsigned> const & route) {
    json jr = json::array();
    for (auto const & i : route) {
        jr.push_back(i);
    }
    return jr;
}

json vdom_element::to_json(list<unsigned> const & route) {
    json entry;
    entry["t"] = m_tag;
    entry["a"] = m_attrs;

    for (auto const & x : m_events) {
        entry["e"][x.first]["r"] = route_to_json(route);
        entry["e"][x.first]["h"] = json(x.second);
    }
    entry["c"] = json::array();
    for (vdom & v : m_children) {
        entry["c"].push_back(v.to_json(route));
    }
    if (m_tooltip) {
        entry["tt"] = (*m_tooltip).to_json(route);
    }
    return entry;
}

struct filter_map_action_hook : public hook_cell {
    ts_vm_obj const m_map;
    ts_vm_obj m_props;
    virtual void initialize(vm_obj const & props) override {
        m_props = props;
    }
    virtual bool reconcile(vm_obj const & props, hook const &) override {
        m_props = props;
        return true;
    }
    virtual optional<vm_obj> action(vm_obj const & action, widget_context &) override {
        vm_obj props = m_props.to_vm_obj();
        lean_assert(props);
        vm_obj o = invoke(m_map.to_vm_obj(), props, action);
        return get_optional(o);
    }
    std::string to_string() { return "filter_map_action"; }
    filter_map_action_hook(ts_vm_obj const map): m_map(map) {}
};

struct map_props_hook: public hook_cell {
    ts_vm_obj const m_map;
    virtual vm_obj get_props(vm_obj const & props) override {
        return invoke(m_map.to_vm_obj(), props);
    }
    std::string to_string() { return "map_props"; }
    map_props_hook(ts_vm_obj const map): m_map(map) {}
};

struct with_should_update_hook : public hook_cell {
    ts_vm_obj const m_su;
    ts_vm_obj m_props;
    virtual void initialize(vm_obj const & props) override {
        m_props = props;
    }
    virtual bool reconcile(vm_obj const & new_props, hook const & previous) override {
        with_should_update_hook const * prev = dynamic_cast<with_should_update_hook const *>(previous.get());
        if (!prev) {return true;}
        vm_obj prev_props = (prev->m_props).to_vm_obj();
        if (!prev_props) {return true;}
        m_props = new_props;
        return to_bool(invoke(m_su.to_vm_obj(), prev_props, new_props));
    }
    std::string to_string() { return "should_update"; }
    with_should_update_hook(ts_vm_obj const su): m_su(su) {}
};

struct stateful_hook : public hook_cell {
    ts_vm_obj const m_init;
    ts_vm_obj const m_props_changed;
    ts_vm_obj const m_update;
    optional<ts_vm_obj> m_props;
    optional<ts_vm_obj> m_state;
    void initialize(vm_obj const & props) override {
        if (!m_state || !m_props) {
            m_state = optional<ts_vm_obj>(invoke(m_init.to_vm_obj(), props));
        } else {
            vm_obj r = invoke(m_props_changed.to_vm_obj(), (*m_props).to_vm_obj(), props, (*m_state).to_vm_obj());
            m_state = optional<ts_vm_obj>(r);
        }
        m_props = optional<ts_vm_obj>(props);
    }
    bool reconcile(vm_obj const & props, hook const & previous) override {
        stateful_hook const * prev = dynamic_cast<stateful_hook const *>(previous.get());
        // assume the props have changed
        if (prev) {
            m_state = prev->m_state;
            m_props = prev->m_props;
        }
        initialize(props);
        return true;
    }
    vm_obj get_props(vm_obj const & props) override {
        if (!m_state) {initialize(props);}
        return mk_vm_pair((*m_state).to_vm_obj(), props);
    }
    optional<vm_obj> action(vm_obj const & action, widget_context &) override {
        lean_assert(m_state);
        lean_assert(m_props);
        vm_obj r = invoke(m_update.to_vm_obj(), (*m_props).to_vm_obj(), (*m_state).to_vm_obj(), action);
        m_state = cfield(r, 0);
        return get_optional(cfield(r, 1));
    }
    std::string to_string() { return "stateful"; }
    stateful_hook(vm_obj const & init, vm_obj const & pc, vm_obj const & update) : m_init(init), m_props_changed(pc), m_update(update) {}
};

struct effects_hook : public hook_cell {
    ts_vm_obj const m_emit;
    optional<ts_vm_obj> m_props;
    effects_hook(vm_obj const & emit): m_emit(emit) {}
    void initialize(vm_obj const & props) override {
        m_props = optional<ts_vm_obj>(props);
    }
    optional<vm_obj> action(vm_obj const & action, widget_context & ctx) override {
        lean_assert(m_props);
        vm_obj es = invoke(m_emit.to_vm_obj(), (*m_props).to_vm_obj(), action);
        ctx.m_effects.push_back(es);
        return optional<vm_obj>(action);
    }
};

component_instance::component_instance(vm_obj const & component, vm_obj const & props, list<unsigned> const & route):
  m_props(props), m_route(route) {
    m_id = g_fresh_component_instance_id.fetch_add(1) + 1;
    m_reconcile_count = 0;
    m_component_hash = hash(component);
    vm_obj c = component;
    while (cidx(c) != component_idx::pure) {
        switch (cidx(c)) {
            case component_idx::pure: break;
            case component_idx::filter_map_action:
                m_hooks.push_back(hook(new filter_map_action_hook(cfield(c, 0))));
                c = cfield(c, 1);
                break;
            case component_idx::map_props:
                m_hooks.push_back(hook(new map_props_hook(cfield(c, 0))));
                c = cfield(c, 1);
                break;
            case component_idx::with_should_update:
                m_hooks.push_back(hook(new with_should_update_hook(cfield(c, 0))));
                c = cfield(c, 1);
                break;
            case component_idx::with_state:
                m_hooks.push_back(hook(new stateful_hook(cfield(c, 0), cfield(c, 1), cfield(c, 2))));
                c = cfield(c, 3);
                break;
            case component_idx::with_effects:
                m_hooks.push_back(hook(new effects_hook(cfield(c, 0))));
                c = cfield(c, 1);
                break;
            default:
                lean_unreachable();
                break;
        }
    }
    m_view = cfield(c, 0);
}

void component_instance::render() {
    lean_assert(m_has_initialized);
    std::vector<component_instance *> children;
    event_handlers handlers;
    vm_obj props = m_inner_props.to_vm_obj();
    vm_obj view = invoke(m_view.to_vm_obj(), props);
    std::vector<vdom> elements = render_html_list(view, children, handlers, cons(m_id, m_route));
    std::vector<vdom> old_elements = m_render;
    reconcile_children(elements, old_elements);
    m_handlers = handlers;
    m_children = children;
    m_render = elements;
    m_has_rendered = true;
}

void component_instance::reconcile(vdom const & old) {
    component_instance const * ci_old = dynamic_cast<component_instance *>(old.raw());
    // If they contain vm_externals which are not hashable then we assume they are the same component.
    // This is acceptable behaviour for now. It just means that the component won't always
    // update correctly if a non-prop dependency of a component changes.
    // But users of components should be using Props anyway so there is a workaround.
    if (ci_old && ci_old->m_component_hash == m_component_hash && m_hooks.size() == ci_old->m_hooks.size()) {
        lean_assert(ci_old->m_has_initialized);
        // if the components are the same:
        vm_obj p_new = m_props.to_vm_obj();
        vm_obj p_old = ci_old->m_props.to_vm_obj();
        bool should_update = true;
        for (unsigned i = 0; i < m_hooks.size(); i++) {
            if (should_update) {
                bool result = m_hooks[i]->reconcile(p_new, ci_old->m_hooks[i]);
                if (!result) {
                    should_update = false;
                }
            } else {
                // a prior hook decided that later hooks shouldn't update, so we
                // assume that the old hooks are valid here.
                m_hooks[i] = ci_old->m_hooks[i];
            }
            p_new = m_hooks[i]->get_props(p_new);
        }
        m_inner_props = p_new;
        m_has_initialized = true;
        m_id              = ci_old->m_id;

        if (!should_update) {
            // the props are equal and the state didn't change, so we can just keep the old rendering.
            m_children        = ci_old->m_children;
            m_render          = ci_old->m_render;
            m_handlers        = ci_old->m_handlers;
            m_has_rendered    = true;
            m_reconcile_count = ci_old->m_reconcile_count + 1;
            lean_assert(m_route == ci_old->m_route);
        } else {
            // the props have changed, so we need to rerender this component.
            render();
        }
    } else {
        // The old component is completely different, so render as a fresh component.
        initialize();
        render();
    }
}

void component_instance::initialize() {
    vm_obj p = m_props.to_vm_obj();
    for (auto h : m_hooks) {
        h->initialize(p);
        p = h->get_props(p);
    }
    m_inner_props = p;
    m_has_initialized = true;
}

void component_instance::compute_props() {
    vm_obj props = m_props.to_vm_obj();
    for (auto h : m_hooks) {
        props = h->get_props(props);
    }
    m_inner_props = props;
}

json component_instance::to_json(list<unsigned> const & route) {
    if (!m_has_initialized) {
        initialize();
    }
    if (!m_has_rendered) {
        render();
    }
    json children = json::array();
    for (vdom const & x : m_render) {
        children.push_back(x.to_json(cons(m_id, route)));
    }
    json result;
    result["c"] = children;
    return result;
}

optional<vm_obj> component_instance::handle_action(vm_obj const & action, widget_context & ctx) {
        optional<vm_obj> result = optional<vm_obj>(action);
        for (int i = m_hooks.size() - 1; i >= 0; i--) {
            if (!result) {break;}
            result = m_hooks[i]->action(*result, ctx);
        }
        compute_props();
        render();
        return result;
}

optional<vm_obj> component_instance::handle_event(list<unsigned> const & route, unsigned handler_id, vm_obj const & event_args, widget_context & ctx) {
    if (empty(route)) {
        if (m_handlers.find(handler_id) == m_handlers.end()) {
            throw invalid_handler();
        }
        vm_obj handler = m_handlers[handler_id].to_vm_obj();
        vm_obj action = (invoke(handler, event_args));
        return handle_action(action, ctx);
    }
    for (auto c : m_children) {
        if (c->m_id == head(route)) {
            optional<vm_obj> a = c->handle_event(tail(route), handler_id, event_args, ctx);
            if (a) {
                return handle_action(*a, ctx);
            } else {
                return optional<vm_obj>();
            }
        }
    }
    // given component no longer exists. This happens if the ui is updated but there are events from an old vdom
    throw invalid_handler();
}

component_instance * component_instance::get_child(unsigned id) {
    for (auto c : m_children) {
        if (c->m_id == id) { return c; }
    }
    return nullptr;
}

void reconcile_children(std::vector<vdom> & new_elements, std::vector<vdom> const & olds) {
    std::vector<vdom> old_elements = olds;
    for (unsigned i = 0; i < new_elements.size(); i++) {
        // [note] you get weird behaviour if multiple things have the same key or if only some elements have keys
        // but this is also true in React so I am not too worried about it as long as it doesn't crash.
        // [todo] add a warning if keys are duplicated or only present on some objects.
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


void render_event(std::string const & name, vm_obj const & handler, std::map<std::string, unsigned> & events, event_handlers & handlers) {
    unsigned handler_id = handlers.size();
    events[name] = handler_id;
    handlers[handler_id] = handler;
}

vdom render_element(vm_obj const & elt, std::vector<component_instance*> & components, event_handlers & handlers, list<unsigned> const & route) {
    // | element      {α : Type} (tag : string) (attrs : list (attr α)) (children : list (html α)) : html α
    std::string tag = to_string(cfield(elt, 0));
    vm_obj v_attrs = cfield(elt, 1);
    vm_obj v_children = cfield(elt, 2);
    json attributes;
    std::map<std::string, unsigned> events;
    optional<vdom> tooltip;
    while (!is_simple(v_attrs)) {
        vm_obj attr = head(v_attrs);
        v_attrs = tail(v_attrs);
        switch (cidx(attr)) {
            case attr_idx::val: { // val {\a} : string -> string -> attr
                std::string key = to_string(cfield(attr, 0));
                std::string value = to_string(cfield(attr, 1));
                // [note] className fields should be merged.
                if (key == "className" && attributes.find(key) != attributes.end()) {
                    std::string cn = attributes[key];
                    cn += " ";
                    cn += value;
                    attributes[key] = cn;
                } else {
                    attributes[key] = value;
                }
                break;
            } case attr_idx::mouse_event: {// on_mouse_event {\a} : mouse_event_kind -> (unit -> Action) -> html.attr
                int mouse_event_kind = cidx(cfield(attr, 0));
                vm_obj handler = cfield(attr, 1);
                switch (mouse_event_kind) {
                    case 0: render_event("onClick",      handler, events, handlers); break;
                    case 1: render_event("onMouseEnter", handler, events, handlers); break;
                    case 2: render_event("onMouseLeave", handler, events, handlers); break;
                    default: lean_unreachable();
                }
                break;
            } case attr_idx::style: { // style {a} : list (string × string) → html.attr
                auto l = cfield(attr, 0);
                while (!is_simple(l)) {
                    auto h = head(l);
                    auto k = to_string(cfield(h, 0));
                    auto v = to_string(cfield(h, 1));
                    attributes["style"][k] = v;
                    l = tail(l);
                }
                break;
            } case attr_idx::tooltip: { // tooltip {a} :  html Action → html.attr
                auto content = cfield(attr, 0);
                vdom tooltip_child = render_html(content, components, handlers, route);
                tooltip = optional<vdom>(tooltip_child);
                break;
            } case attr_idx::text_change_event: { // text_change_event {a} : (string -> Action) -> html.attr
                auto handler = cfield(attr, 0);
                render_event("onChange", handler, events, handlers);
                break;
            } default : {
                lean_unreachable();
                break;
            }
        }
    }
    std::vector<vdom> children = render_html_list(v_children, components, handlers, route);
    return vdom(new vdom_element(tag, attributes, events, children, tooltip));
}

vdom render_html(vm_obj const & html, std::vector<component_instance*> & components, event_handlers & handlers, list<unsigned> const & route) {
    switch (cidx(html)) {
        case html_idx::element: { // | of_element {α : Type} (tag : string) (attrs : list (attr α)) (children : list (html α)) : html α
            vdom elt = render_element(html, components, handlers, route);
            return elt;
        } case html_idx::of_string: { // | of_string    {α : Type} : string → html α
            return vdom(new vdom_string(to_string(cfield(html, 0))));
        } case html_idx::of_component: { // | of_component {α : Type} {Props : Type} : Props → component Props α → html α
            vm_obj props = cfield(html, 0);
            vm_obj comp  = cfield(html, 1);
            component_instance * c = new component_instance(comp, props, route);
            components.push_back(c);
            return vdom(c);
        } default: {
            lean_unreachable();
        }
    }
}

std::vector<vdom> render_html_list(vm_obj const & htmls, std::vector<component_instance*> & components, event_handlers & handlers, list<unsigned> const & route) {
    std::vector<vdom> elements;
    vm_obj l = htmls;
    while (!is_simple(l)) {
        vdom x = render_html(head(l), components, handlers, route);
        elements.push_back(x);
        l = tail(l);
    }
    return elements;
}

json to_file_name(vm_obj const & a) {
    if (is_none(a)) {
        return nullptr;
    } else {
        return to_string(get_some_value(a));
    }
}

void get_effects(vm_obj const & o_effects, json & result) {
    buffer<vm_obj> effects;
    vm_obj l = o_effects;
    while (!is_simple(l)) {
        effects.push_back(head(l));
        l = tail(l);
    }
    for (auto e : effects) {
        switch (cidx(e)) {
            case effect_idx::insert_text: {
                result.push_back({
                    {"kind", "insert_text"},
                    {"text", to_string(cfield(e, 0))}
                });
                break;
            } case effect_idx::reveal_position: {
                auto pos = to_pos_info(cfield(e, 1));
               result.push_back({
                    {"kind", "reveal_position"},
                    {"file_name", to_file_name(cfield(e, 0))},
                    {"line", pos.first},
                    {"column", pos.second}
                });
                break;
            } case effect_idx::highlight_position: {
                auto pos = to_pos_info(cfield(e, 1));
                result.push_back({
                    {"kind", "highlight_position"},
                    {"file_name", to_file_name(cfield(e, 0))},
                    {"line", pos.first},
                    {"column", pos.second}
                });
                break;
            } case effect_idx::clear_highlighting: {
                result.push_back({
                    {"kind", "clear_highlighting"}
                });
                break;
            } case effect_idx::copy_text: {
                result.push_back({
                    {"kind", "copy_text"},
                    {"text", to_string(cfield(e, 0))}
                });
                break;
            } case effect_idx::custom: {
                result.push_back({
                    {"kind", "custom"},
                    {"key", to_string(cfield(e, 0))},
                    {"value", to_string(cfield(e, 1))}
                });
                break;
            } default: {
                lean_unreachable();
            }
        }
    }
}



void initialize_widget() {}

void finalize_widget() {}

}
