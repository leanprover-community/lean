/*
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
*/
#pragma once
#include <map>
#include <algorithm>
#include <vector>
#include <string>
#include "util/list.h"
#include "util/pair.h"
#include "kernel/expr.h"
#include "library/vm/vm.h"
#include "library/io_state_stream.h"
#include "frontends/lean/json.h"

namespace lean {

typedef std::map<unsigned, ts_vm_obj> event_handlers;

class vdom;

enum class vdom_kind { String, Element, ComponentInstance};

class vdom_cell {
  MK_LEAN_RC();
  void dealloc() { delete this; }
protected:
    friend vdom;
public:
  vdom_cell() : m_rc(0) {}
  virtual ~vdom_cell() {}
  virtual json to_json(list<unsigned> const &) { return json(); };
  virtual optional<std::string> key() { return optional<std::string>(); };
  virtual void reconcile(vdom const &) { }
};

class vdom {
private:
  vdom_cell * m_ptr;
  friend class vdom_cell;
public:
  vdom(vdom_cell * ptr) : m_ptr(ptr) { lean_assert(m_ptr);  m_ptr->inc_ref(); }
  vdom(vdom const & s) : m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
  vdom(vdom && s) : m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
  vdom() : m_ptr(nullptr) {}
  ~vdom() {if (m_ptr) m_ptr->dec_ref(); }
  vdom & operator=(vdom const & s) { LEAN_COPY_REF(s); }
  vdom & operator=(vdom && s) { LEAN_MOVE_REF(s); }
  void reconcile(vdom const & old_vdom) { m_ptr->reconcile(old_vdom); }
  vdom_cell * raw() const { return m_ptr; }
  json to_json(list<unsigned> const & route = {}) const { return m_ptr->to_json(route); }
  optional<std::string> key() { return m_ptr->key(); }
};

struct vdom_element : public vdom_cell {
    std::string m_tag;
    json m_attrs;
    std::map<std::string, unsigned> m_events;
    std::vector<vdom> m_children;
    optional<vdom> m_tooltip;
    vdom_element(std::string const & tag, json const & attrs, std::map<std::string, unsigned> events, std::vector<vdom> const & children, optional<vdom> const & tooltip)
      : m_tag(tag), m_attrs(attrs), m_events(events), m_children(children), m_tooltip(tooltip) {}
    optional<std::string> key() override;
    void reconcile(vdom const & old_vdom) override;
    json to_json(list<unsigned> const & route) override;
};

struct vdom_string : public vdom_cell {
    std::string m_val;
    vdom_string(std::string const & val) : m_val(val) {}
    json to_json(list<unsigned> const &) override { return m_val; }
};

class hook_cell;
typedef std::shared_ptr<hook_cell> hook;
class hook_cell {
public:
  hook_cell() {}
  virtual ~hook_cell() {}
  /** Called for a fresh component with no previous value. */
  virtual void initialize(vm_obj const &) {};
  /** Update the hook based on the previous value.
   * This should be called whenever the props change.
   * If it returns true then the view should rerender.
   * If false is returned then all of the later hooks will not be reconciled.
   */
  virtual bool reconcile(vm_obj const &, hook const &) { return true; };
  virtual vm_obj get_props(vm_obj const & props) { return props; }
  virtual optional<vm_obj> action(vm_obj const & action) { return optional<vm_obj>(action); };
  virtual std::string to_string() {return "hook";}
};

class component_instance : public vdom_cell {
  // set on construction
  unsigned int m_component_hash;
  ts_vm_obj m_view;
  ts_vm_obj const m_props;
  std::vector<hook> m_hooks;
  unsigned m_id;
  // set on initialisation / reconciliation
  bool m_has_initialized = false;
  ts_vm_obj m_inner_props;
  list<unsigned> m_route;
  unsigned m_reconcile_count = 0;
  // set on rendering
  bool m_has_rendered = false;
  std::vector<component_instance *> m_children;
  std::vector<vdom> m_render;
  event_handlers m_handlers;

  list<unsigned> child_route() {return cons(m_id, m_route); }
  /** convert an inner action to an outer action */
  optional<vm_obj> handle_action(vm_obj const & a);
  /** Compute the vdom tree for this component.
   * Assumes that initialize or reconcile was called. */
  void render();
  void compute_props();
  void reconcile(vdom const & old);
  /** Perform initialisation step:
   *  initialise the hooks, including setting states.
   */
  void initialize();

  component_instance * get_child(unsigned id);

public:
  json to_json(list<unsigned> const & route) override;

  optional<vm_obj> handle_event(list<unsigned> const & route, unsigned handler_id, vm_obj const & eventArgs);
  component_instance(vm_obj const & c, vm_obj const & props, list<unsigned> const & route = list<unsigned>());
  unsigned id() {return m_id;}
};

/** Iterates, new_elements and old_elements, mutating both (but old_elements is passed by value so that doesn't matter).
 *  `new_children` is mutated so that they point to vdom components that were successfully reconciled with the old version.
 */
void reconcile_children(std::vector<vdom> & new_elements, std::vector<vdom> const & old_elements);

// void render_attr(vm_obj const & attr, json & attributes, std::map<std::string, unsigned> & events, event_handlers & handlers);
vdom render_element(vm_obj const & elt, std::vector<component_instance*> & components, event_handlers & handlers, list<unsigned> const & route);
vdom render_html(vm_obj const & html, std::vector<component_instance*> & components, event_handlers & handlers, list<unsigned> const & route);
std::vector<vdom> render_html_list(vm_obj const & htmls, std::vector<component_instance*> & components, event_handlers & handlers, list<unsigned> const & route);

void initialize_widget();
void finalize_widget();

/** This is thrown when an event is recieved from the client but the route list and handler do not point to a valid handler on the vdom.
 * This can occur as the result of a bug in the client code, but it can also occur in multi-thread scenarios where multiple widget_events are
 * sent in parallel and the vdom has updated before the second widget_event has been processed.
 */
class invalid_handler : public exception {
public:
    invalid_handler() {}
    virtual ~invalid_handler() noexcept {}
    virtual char const * what() const noexcept { return "invalid widget event handler"; }
    virtual throwable * clone() const { return new invalid_handler(); }
    virtual void rethrow() const { throw *this; }
};

}
