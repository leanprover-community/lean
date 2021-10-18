/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Leonardo de Moura, Sebastian Ullrich
*/
#if defined(LEAN_JSON)
// Remark: gcc 7 produces a warning at json.hpp
// We believe it is a spurious warning
#if defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wuninitialized"
#endif

#include <list>
#include <string>
#include <vector>
#include <algorithm>
#include <clocale>
#include "frontends/lean/module_parser.h"
#include "library/library_task_builder.h"
#include "util/lean_path.h"
#include "util/sexpr/option_declarations.h"
#include "util/timer.h"
#include "util/line_endings.h"
#include "library/mt_task_queue.h"
#include "library/st_task_queue.h"
#include "library/attribute_manager.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/interactive.h"
#include "frontends/lean/completion.h"
#include "frontends/lean/elaborator.h"
#include "shell/server.h"

#include "kernel/type_checker.h"
#include "kernel/expr_sets.h"
#include "kernel/for_each_fn.h"
#include "library/tactic/tactic_evaluator.h"
#include "library/tactic/intro_tactic.h"
#include "library/unfold_macros.h"
#include "library/compiler/rec_fn_macro.h"
#include "library/library_task_builder.h"
#include "library/st_task_queue.h"
#include "library/mt_task_queue.h"
#include "frontends/lean/json.h"
#include "frontends/lean/cmd_table.h"
#include "library/check.h"


namespace lean {
struct all_messages_msg {
    std::vector<message> m_msgs;

    json to_json_response() const {
        auto msgs = json::array();
        for (auto & msg : m_msgs)
            msgs.push_back(json_of_message(msg));

        json j;
        j["response"] = "all_messages";
        j["msgs"] = msgs;
        return j;
    }
};

region_of_interest::intersection_result region_of_interest::intersects(location const & loc) const {
    if (loc.m_file_name.empty()) return InROI;
    if (!m_open_files || !m_open_files->count(loc.m_file_name)) return NoIntersection;
    auto & visible_lines = m_open_files->at(loc.m_file_name);
    bool above_roi = false;
    for (auto & lr : visible_lines) {
        if (std::max(lr.m_begin_line, loc.m_range.m_begin.first)
            <= std::min(lr.m_end_line, loc.m_range.m_end.first)) {
            return InROI;
        }
        if (loc.m_range.m_begin.first <= lr.m_end_line) above_roi = true;
    }
    if (above_roi) return AboveROI;
    return visible_lines.empty() ? OpenFile : VisibleFile;
}

bool region_of_interest::should_report(location const & loc) const {
    auto isect = intersects(loc);
    switch (m_check_mode) {
        case Nothing: return false;
        case VisibleLines: return isect >= InROI;
        case VisibleLinesAndAbove: case VisibleFiles:
            return isect >= VisibleFile;
        case OpenFiles: return isect >= OpenFile;
        default: return true;
    }
}

optional<unsigned> region_of_interest::get_priority(log_tree::node const & n) const {
    auto isect = intersects(n.get_location());
    optional<unsigned> yes(isect >= InROI ? n.get_detail_level() : n.get_detail_level() + log_tree::MaxLevel);
    optional<unsigned> no;

    switch (m_check_mode) {
        case Nothing: return no;
        case VisibleLines: return (isect >= InROI && n.get_detail_level() < log_tree::CrossModuleLintLevel) ? yes : no;
        case VisibleLinesAndAbove: return isect >= AboveROI ? yes : no;
        case VisibleFiles: return isect >= VisibleFile ? yes : no;
        case OpenFiles: return isect >= OpenFile ? yes : no;
        default: return yes;
    }
}

class server::message_handler {
    server * m_srv;
    log_tree * m_lt;

    mutex m_mutex;
    std::unordered_set<std::string> m_dirty_files;
    bool m_full_refresh_scheduled = false;
    std::unique_ptr<single_timer> m_timer;

public:
    message_handler(server * srv, log_tree * lt, bool use_timer) : m_srv(srv), m_lt(lt) {
        if (use_timer) m_timer.reset(new single_timer);
    }

    std::vector<message> get_messages_core(region_of_interest const & roi) {
        std::vector<message> msgs;
        m_lt->for_each([&] (log_tree::node const & n) {
            if (roi.should_report(n.get_location())) {
                for (auto & e : n.get_entries()) {
                    if (auto msg = dynamic_cast<message const *>(e.get())) {
                        if (roi.should_report(msg->get_location()))
                            msgs.push_back(*msg);
                    }
                }
                return true;
            } else {
                return false;
            }
        });
        return msgs;
    }

    void schedule_refresh() {
#if defined(LEAN_MULTI_THREAD)
        if (m_timer) {
            m_full_refresh_scheduled = true;
            m_timer->set(chrono::steady_clock::now() + chrono::milliseconds(100), [&] {
                    unique_lock<mutex> lock(m_mutex);
                    m_full_refresh_scheduled = false;
                    m_dirty_files.clear();
                    auto roi = m_srv->get_roi();
                    lock.unlock();

                    m_srv->send_msg(all_messages_msg{get_messages_core(roi)});
                }, false);
        }
#endif
        if (!m_full_refresh_scheduled) {
            m_dirty_files.clear();
            m_srv->send_msg(all_messages_msg{get_messages_core(m_srv->get_roi())});
        }
    }

    void on_event(std::vector<log_tree::event> const & events) {
        unique_lock<mutex> lock(m_mutex);
        auto roi = m_srv->get_roi();
        for (auto & e : events) {
            switch (e.m_kind) {
                case log_tree::event::EntryAdded:
                case log_tree::event::EntryRemoved:
                    if (auto msg = dynamic_cast<message const *>(e.m_entry.get())) {
                        if (roi.should_report(msg->get_location())) {
                            m_dirty_files.insert(msg->get_file_name());
                        }
                    }
                    break;

                default: break;
            }
        }
        if (!m_dirty_files.empty()) {
            schedule_refresh();
        }
    }

    void on_new_roi() {
        unique_lock<mutex> lock(m_mutex);
        schedule_refresh();
    }
};

struct current_tasks_msg {
    std::vector<json> m_tasks;
    optional<json> m_cur_task;
    bool m_is_running = false;

    json to_json_response() const {
        json j;
        j["response"] = "current_tasks";
        j["is_running"] = m_is_running;
        if (m_cur_task) j["cur_task"] = *m_cur_task;
        j["tasks"] = m_tasks;
        return j;
    }

    static json json_of_task(log_tree::node const & t) {
        json j;
        j["file_name"] = t.get_location().m_file_name;
        auto pos = t.get_location().m_range.m_begin;
        j["pos_line"] = pos.first;
        j["pos_col"] = pos.second;
        auto end_pos = t.get_location().m_range.m_end;
        j["end_pos_line"] = end_pos.first;
        j["end_pos_col"] = end_pos.second;
        j["desc"] = t.get_description();
        return j;
    }
};

class server::tasks_handler {
    server * m_srv;
    log_tree * m_lt;

    mutex m_mutex;
    std::unique_ptr<single_timer> m_timer;

public:
    tasks_handler(server * srv, log_tree * lt, bool use_timer) : m_srv(srv), m_lt(lt) {
        if (use_timer) m_timer.reset(new single_timer);
    }

    void submit_core(unsigned prio, log_tree::node const & n) {
        if (auto prod = n.get_producer()) {
            taskq().submit(prod, prio);
        }
    }

    void resubmit_core() {
        auto roi = m_srv->get_roi();
        m_srv->m_lt.for_each([&] (log_tree::node const & n) {
            if (auto prio = roi.get_priority(n)) {
                submit_core(*prio, n);
                return true;
            } else {
                return false;
            }
        });
    }

    current_tasks_msg mk_tasks_msg() {
        current_tasks_msg msg;
        auto roi = m_srv->get_roi();
        m_lt->for_each([&] (log_tree::node const & n) {
            if (roi.get_priority(n)) {
                if (n.get_producer()) {
                    msg.m_is_running = true;
                    msg.m_tasks.push_back(current_tasks_msg::json_of_task(n));
                    return false;
                } else {
                    return true;
                }
            } else {
                return false;
            }
        });
        return msg;
    }

    void schedule_refresh() {
#if defined(LEAN_MULTI_THREAD)
        if (m_timer) {
            m_timer->set(chrono::steady_clock::now() + chrono::milliseconds(200), [&] {
                m_srv->send_msg(mk_tasks_msg());
            }, false);
        }
#endif
    }

    void on_event(std::vector<log_tree::event> const & events) {
        optional<region_of_interest> roi;
        bool need_refresh = false;
        for (auto & e : events) {
            switch (e.m_kind) {
                case log_tree::event::ProducerSet:
                    if (!roi) roi = m_srv->get_roi();
                    if (auto prio = roi->get_priority(e.m_node)) {
                        submit_core(*prio, e.m_node);
                        need_refresh = true;
                    }
                    break;
                case log_tree::event::StateChanged:
                    if (!roi) roi = m_srv->get_roi();
                    if (roi->get_priority(e.m_node))
                        need_refresh = true;
                    break;

                default:
                    break;
            }
        }
        if (need_refresh) {
            unique_lock<mutex> lock(m_mutex);
            schedule_refresh();
        }
    }

    void on_new_roi() {
        resubmit_core();
        unique_lock<mutex> lock(m_mutex);
        schedule_refresh();
    }
};

void server::setup_handlers(unsigned num_threads){
    m_msg_handler.reset(new message_handler(this, &m_lt, num_threads > 0));
    m_tasks_handler.reset(new tasks_handler(this, &m_lt, num_threads > 0));

    m_lt.add_listener([&] (std::vector<log_tree::event> const & evs) {
        m_msg_handler->on_event(evs);
        m_tasks_handler->on_event(evs);
    });
}

void server::clear_handlers(){
    m_lt.clear_listeners();
    m_msg_handler.reset(nullptr);
    m_tasks_handler.reset(nullptr);
}

server::server(unsigned num_threads, search_path const & path, environment const & initial_env, io_state const & ios,
        bool use_old_oleans,
        bool report_widgets,
        bool quiet,
        bool never_use_olean) :
        m_path(path), m_initial_env(initial_env), m_ios(ios), m_quiet(quiet), m_never_use_olean(never_use_olean) {
    m_ios.set_regular_channel(std::make_shared<stderr_channel>());
    m_ios.set_diagnostic_channel(std::make_shared<stderr_channel>());

    setup_handlers(num_threads);
    scope_global_ios scoped_ios(m_ios);
#if defined(LEAN_MULTI_THREAD)
    if (num_threads == 0) {
        m_tq.reset(new st_task_queue);
    } else {
        m_tq.reset(new mt_task_queue(num_threads));
    }
#else
    m_tq.reset(new st_task_queue());
#endif

    set_task_queue(m_tq.get());
    m_mod_mgr.reset(new module_mgr(this, m_lt.get_root(), m_path, m_initial_env, m_ios));
    m_mod_mgr->set_use_old_oleans(use_old_oleans);
    m_mod_mgr->set_report_widgets(report_widgets);
    set_global_module_mgr(*m_mod_mgr);
    m_mod_mgr->set_server_mode(true);
    m_mod_mgr->set_save_olean(false);
}

server::~server() {
    m_mod_mgr->cancel_all();
    m_tq->evacuate();
}

struct server::cmd_req {
    unsigned m_seq_num = static_cast<unsigned>(-1);
    std::string m_cmd_name;
    json m_payload;
};

struct server::cmd_res {
    cmd_res() {}
    cmd_res(unsigned seq_num, json const & payload) : m_seq_num(seq_num), m_payload(payload) {}
    cmd_res(unsigned seq_num, std::string const & error_msg) : m_seq_num(seq_num), m_error_msg(error_msg) {}

    unsigned m_seq_num = static_cast<unsigned>(-1);
    json m_payload;
    optional<std::string> m_error_msg;

    json to_json_response() const {
        json j;
        if (m_error_msg) {
            j["response"] = "error";
            j["message"] = *m_error_msg;
        } else {
            j = m_payload;
            j["response"] = "ok";
        }
        j["seq_num"] = m_seq_num;
        return j;
    }
};

struct unrelated_error_msg {
    std::string m_msg;

    json to_json_response() const {
        json j;
        j["response"] = "error";
        j["message"] = m_msg;
        return j;
    }
};

// Debugging functions for use in GDB.
server * g_server = nullptr;
void server_dump_log_tree() {
    g_server->get_log_tree().print_to(std::cerr);
}
void server_print_roi() {
    auto roi = g_server->get_roi();
    std::cerr << "mode: " << roi.m_check_mode << std::endl;
    for (auto & f : *roi.m_open_files) {
        std::cerr << f.first << std::endl;
        for (auto & lr : f.second) {
            std::cerr << " " << lr.m_begin_line << "-" << lr.m_end_line << std::endl;
        }
    }
}

void server::run() {
    flet<server *> _(g_server, this);

    scope_global_ios scoped_ios(m_ios);

    /* Leo: we use std::setlocale to make sure decimal period is displayed as ".".
       We added this hack because the json library code used for ensuring this property
       was crashing when compiling Lean on Windows with mingw. */
#if !defined(LEAN_EMSCRIPTEN)
    std::setlocale(LC_NUMERIC, "C");
#endif

    while (true) {
        try {
            std::string req_string;
            std::getline(std::cin, req_string);
            if (std::cin.eof()) return;

            json req = json::parse(req_string);

            handle_request(req);
        } catch (std::exception & ex) {
            send_msg(unrelated_error_msg{ex.what()});
        }
    }
}

void server::handle_request(json const & jreq) {
    cmd_req req;
    req.m_seq_num = jreq.at("seq_num");
    try {
        req.m_cmd_name = jreq.at("command");
        req.m_payload = jreq;
        handle_request(req);
    } catch (std::exception & ex) {
        send_msg(cmd_res(req.m_seq_num, std::string(ex.what())));
    } catch (interrupted &) {
        send_msg(cmd_res(req.m_seq_num, std::string("interrupted")));
    } catch (...) {
        send_msg(cmd_res(req.m_seq_num, std::string("unknown exception")));
    }
}

void server::handle_request(server::cmd_req const & req) {
    std::string command = req.m_cmd_name;

    if (command == "sync") {
        send_msg(handle_sync(req));
    } else if (command == "complete") {
        handle_async_response(req, handle_complete(req));
    } else if (command == "info") {
        handle_async_response(req, handle_info(req));
    } else if (command == "hole") {
        handle_async_response(req, handle_hole(req));
    } else if (command == "try_tactic") {
        handle_async_response(req, handle_try_tactic(req));
    } else if (command == "hole_commands") {
        send_msg(handle_hole_commands(req));
    } else if (command == "all_hole_commands") {
        send_msg(handle_all_hole_commands(req));
    } else if (command == "search") {
        send_msg(handle_search(req));
    } else if (command == "roi") {
        send_msg(handle_roi(req));
    } else if (command == "sleep") {
        chrono::milliseconds small_delay(1000);
        this_thread::sleep_for(small_delay);
    } else if (command == "long_sleep") {
        chrono::milliseconds small_delay(10000);
        this_thread::sleep_for(small_delay);
    } else if (command == "sync_output") {
        taskq().wait_for_finish(this->m_lt.get_root().wait_for_finish());
    } else if (command == "widget_event") {
        handle_async_response(req, handle_widget_event(req));
    } else if (command == "get_widget") {
        handle_async_response(req, handle_get_widget(req));
    } else {
        send_msg(cmd_res(req.m_seq_num, std::string("unknown command")));
    }
}

void server::handle_async_response(server::cmd_req const & req, task<cmd_res> const & res) {
    taskq().submit(task_builder<unit>([this, req, res] {
        try {
            auto msg = get(res);
            msg.m_seq_num = req.m_seq_num;
            send_msg(msg);
        } catch (throwable & ex) {
            send_msg(cmd_res(req.m_seq_num, std::string(ex.what())));
        } catch (interrupted &) {
            send_msg(cmd_res(req.m_seq_num, std::string("interrupted")));
        } catch (...) {
            send_msg(cmd_res(req.m_seq_num, std::string("unknown exception")));
        }
        return unit{};
    }).depends_on(res).build());
}

server::cmd_res server::handle_sync(server::cmd_req const & req) {
    std::string new_file_name = req.m_payload.at("file_name");
    std::string new_content;
    if (req.m_payload.count("content")) {
        new_content = req.m_payload.at("content");
    } else {
        new_content = load_module(new_file_name, /* can_use_olean */ false)->m_contents;
    }

    // NOTE(Vtec234): as of 2020-03-05, hashing all of mathlib takes about .1s on
    // a 2.7GHz cpu, so this should not have observable performance impact.
    unsigned new_hash = hash_data(remove_cr(new_content));

    bool needs_invalidation = true;

    auto & ef = m_open_files[new_file_name];
    if (ef.m_src_hash != new_hash) {
        ef.m_content = new_content;
        ef.m_src_hash = new_hash;
        needs_invalidation = true;
    } else {
        needs_invalidation = false;
    }

    json res;
    if (needs_invalidation) {
        m_mod_mgr->invalidate(new_file_name);
        res["message"] = "file invalidated";
    } else {
        res["message"] = "file unchanged";
    }

    return { req.m_seq_num, res };
}

optional<module_parser_result> get_closest_snapshot(std::shared_ptr<module_info const> const & mod_info, pos_info p) {
    auto res = mod_info->m_snapshots;

    while (res && res->m_next) {
        if (auto next = peek(res->m_next)) {
            if (next->m_range.m_end < p) {
                res = next;
            } else {
                break;
            }
        } else {
            break;
        }
    }

    return res;
}

void parse_breaking_at_pos(module_id const & mod_id, std::shared_ptr<module_info const> mod_info, pos_info pos,
                           bool complete = false) {
    if (auto snap = get_closest_snapshot(mod_info, pos)) {
        // ignore messages from reparsing
        log_tree null;
        scope_log_tree scope_lt(null.get_root());
        snap->m_lt = logtree();
        snap->m_cancel = global_cancellation_token();
        snap->m_next = nullptr;

        auto p = std::make_shared<module_parser>(mod_id, mod_info->m_contents, environment(), mk_dummy_loader());
        p->save_info(false);
        p->use_separate_tasks(false);
        p->break_at_pos(pos, complete);

        p->resume(*snap, {});
    }
}

json server::autocomplete(std::shared_ptr<module_info const> const & mod_info, bool skip_completions,
                          pos_info const & pos0) {
    auto pos = pos0;
    if (pos.second == 0)
        pos.first--;
    pos.second--;
    json j;

    if (auto snap = get_closest_snapshot(mod_info, pos)) {
        try {
            parse_breaking_at_pos(mod_info->m_id, mod_info, pos, true);
        } catch (break_at_pos_exception & e) {
            report_completions(snap->m_snapshot_at_end->m_env, snap->m_snapshot_at_end->m_options,
                               pos0, skip_completions, m_path, mod_info->m_id.c_str(),
                               e, j);
        } catch (throwable & ex) {}
    }
    return j;
}

task<server::cmd_res> server::handle_complete(cmd_req const & req) {
    std::string fn = req.m_payload.at("file_name");
    pos_info pos = {req.m_payload.at("line"), req.m_payload.at("column")};
    bool skip_completions = false;
    if (req.m_payload.count("skip_completions"))
        skip_completions = req.m_payload.at("skip_completions");

    auto mod_info = m_mod_mgr->get_module(fn);

    return task_builder<cmd_res>([=] { return cmd_res(req.m_seq_num, autocomplete(mod_info, skip_completions, pos)); })
        .wrap(library_scopes(log_tree::node()))
        .build();
}

static void get_info_managers(log_tree::node const & n, std::vector<info_manager> & infoms) {
    n.for_each([&] (log_tree::node const & c) {
        for (auto & e : c.get_entries()) {
            if (auto infom = dynamic_cast<info_manager const *>(e.get())) {
                infoms.push_back(*infom);
            }
        }
        return true;
    });
}

std::vector<info_manager> get_info_managers(log_tree const & t) {
    std::vector<info_manager> infoms;
    get_info_managers(t.get_root(), infoms);
    return infoms;
}

json server::info(std::shared_ptr<module_info const> const & mod_info, pos_info const & pos) {
    json j;
    try {
        parse_breaking_at_pos(mod_info->m_id, mod_info, pos);
    } catch (break_at_pos_exception & e) {
        auto opts = m_ios.get_options();
        auto env = m_initial_env;
        if (auto snap = get_closest_snapshot(mod_info, e.m_token_info.m_pos)) {
            env = snap->m_snapshot_at_end->m_env;
            opts = snap->m_snapshot_at_end->m_options;
        }
        report_info(env, opts, m_ios, m_path, *mod_info, get_info_managers(m_lt), pos, e, j);
    } catch (throwable & ex) {}

    return j;
}

task<server::cmd_res> server::handle_widget_event(server::cmd_req const & req) {
    // [todo] Need some help on how multithreading works. Should all events happen synchronously?
    // what happens if it is processing an event and then a second event occurs? There needs to be an event queue.
    // there should at least be a thread lock on modifying a vdom object.
    std::string fn = req.m_payload.at("file_name");
    pos_info pos = {req.m_payload.at("line"), req.m_payload.at("column")};
    unsigned id = req.m_payload.at("id");

    auto mod_info = m_mod_mgr->get_module(fn);

    return task_builder<cmd_res>([=] {
        json j;
        update_widget(*mod_info, get_info_managers(m_lt), pos, id, j, req.m_payload);
        return cmd_res(req.m_seq_num, j);
    }).wrap(library_scopes(log_tree::node())).build();
}

task<server::cmd_res> server::handle_get_widget(server::cmd_req const & req) {
    std::string fn = req.m_payload.at("file_name");
    pos_info pos = {req.m_payload.at("line"), req.m_payload.at("column")};
    unsigned id = req.m_payload.at("id");

    auto mod_info = m_mod_mgr->get_module(fn);

    return task_builder<cmd_res>([=] {
        json j;
        get_widget(*mod_info, get_info_managers(m_lt), pos, id, j);
        return cmd_res(req.m_seq_num, j);
    }).wrap(library_scopes(log_tree::node())).build();
}

task<server::cmd_res> server::handle_info(server::cmd_req const & req) {
    std::string fn = req.m_payload.at("file_name");
    pos_info pos = {req.m_payload.at("line"), req.m_payload.at("column")};

    auto mod_info = m_mod_mgr->get_module(fn);

    return task_builder<cmd_res>([=] {
        return cmd_res(req.m_seq_num, info(mod_info, pos));
    }).wrap(library_scopes(log_tree::node())).build();
}

tactic_state apply(tactic_state& some_ts, snapshot const & snapshot, const std::string& tactic_str) {
    // parse
    std::istringstream input_stream("`[" + tactic_str + "]");
    lean::parser some_parser(snapshot.m_env, get_global_ios(), mk_dummy_loader(), input_stream, "dummy file");
    some_parser.from_snapshot(snapshot);
    some_parser.scan();

    auto pre_expr = (some_parser.no_error_recovery_scope(), some_parser.parse_expr());

    //elaborate (from tactic_to_expr)
    optional<metavar_decl> g = some_ts.get_main_goal_decl();
    elaborator elab(mk_type_context_for(some_ts), some_ts.get_options(), some_ts.decl_name(), false /* recover_from_errors */);
    expr parsed_expr = elab.elaborate(resolve_names(some_ts.env(), g->get_context(), pre_expr));
    auto elab_mctx = elab.mctx();
    parsed_expr = elab_mctx.instantiate_mvars(parsed_expr);

    //evaluate `[...] tactic into a tactic unit
    vm_state S(some_ts.env(), some_ts.get_options());
    metavar_context s_mctx = some_ts.mctx();
    parsed_expr = s_mctx.instantiate_mvars(parsed_expr);
    environment aux_env = S.env();
    name eval_aux_name = mk_unused_name(aux_env, "_eval_expr");
    expr expected_type = mk_tactic_unit();
    auto cd = check(aux_env, mk_definition(aux_env, eval_aux_name, {}, expected_type, parsed_expr, true, false));
    auto declaration = cd.get_declaration();
    expr evaled_expr = declaration.get_value();

    // run the tactic unit on the current tactic_state
    auto type_context = mk_type_context_for(some_ts);
    auto evaluator = tactic::evaluator(type_context, some_ts.get_options(), false);
    vm_obj r = evaluator(evaled_expr, some_ts);
    auto maybe_ts = tactic::is_success(r);
    if (maybe_ts) {
        return maybe_ts.value();
    }
    throw std::runtime_error("apply tactic failed");
}


json server::try_tactic_command(std::shared_ptr<module_info const> const & mod_info, std::string const & tactic,
                                pos_info const & pos, unsigned widget_id) {
    json j;
    widget_info * w = nullptr;

    auto snap = get_closest_snapshot(mod_info, pos)->m_snapshot_at_end;
    auto info_managers = get_info_managers(m_lt);

    for (info_manager const & infom : info_managers) {
        if (infom.get_file_name() == mod_info->m_id) {
            auto ds = infom.get_info(pos);
            if (!ds) continue;
            for (info_data const & d : *ds) {
                if (auto cw = is_widget_info(d)) {
                    if (cw->has_widget() && cw->id() == widget_id) {
                        w = const_cast<widget_info *>(cw);
                        break;
                    }
                }
            }
        }
        if (w) break; // found what we want
    }
    if (w) {
        auto ts = w->get_tactic_state();
        j["tactic"] = tactic;
        try{
            auto result_ts = apply(ts, *snap, tactic);
            j["validity"] = true;
            j["next_ts"] = (sstream() << result_ts.pp()).str();
        } catch (std::exception& e){
            j["validity"] = false;
            j["error"] = e.what();
        }
    }
    else {
        j["error"] = (sstream() << "Didn't find widget " << widget_id).str();
    }
    return j;
}

task<server::cmd_res> server::handle_try_tactic(cmd_req const & req) {
    std::string fn         = req.m_payload.at("file_name");
    std::string tactic_str = req.m_payload.at("tactic");
    unsigned widget_id     = req.m_payload.at("id");
    pos_info pos           = {req.m_payload.at("line"), req.m_payload.at("column")};
    auto mod_info          = m_mod_mgr->get_module(fn);

    return task_builder<cmd_res>([=] { return cmd_res(req.m_seq_num, try_tactic_command(mod_info, tactic_str, pos, widget_id)); })
        .wrap(library_scopes(log_tree::node()))
        .build();
}

json server::hole_command(std::shared_ptr<module_info const> const & mod_info, std::string const & action,
                          pos_info const & pos) {
    json j;
    std::vector<info_manager> im = get_info_managers(m_lt);
    execute_hole_command(*mod_info, im, pos, action, j);
    return j;
}

task<server::cmd_res> server::handle_hole(cmd_req const & req) {
    std::string action = req.m_payload.at("action");
    std::string fn     = req.m_payload.at("file_name");
    pos_info pos       = {req.m_payload.at("line"), req.m_payload.at("column")};
    auto mod_info      = m_mod_mgr->get_module(fn);

    return task_builder<cmd_res>([=] { return cmd_res(req.m_seq_num, hole_command(mod_info, action, pos)); })
        .wrap(library_scopes(log_tree::node()))
        .build();
}

server::cmd_res server::handle_hole_commands(server::cmd_req const & req) {
    std::string fn     = req.m_payload.at("file_name");
    pos_info pos       = {req.m_payload.at("line"), req.m_payload.at("column")};
    auto mod_info      = m_mod_mgr->get_module(fn);
    std::vector<info_manager> im = get_info_managers(m_lt);
    json j;
    get_hole_commands(*mod_info, im, pos, j);
    return cmd_res(req.m_seq_num, j);
}

server::cmd_res server::handle_all_hole_commands(server::cmd_req const & req) {
    std::string fn     = req.m_payload.at("file_name");
    auto mod_info      = m_mod_mgr->get_module(fn);
    std::vector<info_manager> im = get_info_managers(m_lt);
    json j;
    get_all_hole_commands(*mod_info, im, j);
    return cmd_res(req.m_seq_num, j);
}

server::cmd_res server::handle_search(server::cmd_req const & req) {
    std::string query = req.m_payload.at("query");

    std::vector<pair<std::string, environment>> envs_to_search;
    for (auto & mod : m_mod_mgr->get_all_modules()) {
        envs_to_search.emplace_back(mod->m_id, mod->get_latest_env());
    }

    std::vector<json> results;
    search_decls(query, envs_to_search, m_ios.get_options(), results);

    json j;
    j["results"] = results;

    return cmd_res(req.m_seq_num, j);
}

std::shared_ptr<module_info> server::load_module(module_id const & id, bool can_use_olean) {
    if (m_open_files.count(id)) {
        auto & ef = m_open_files[id];
        return std::make_shared<module_info>(id, ef.m_content, ef.m_src_hash, ef.m_src_hash, module_src::LEAN);
    }
    return m_fs_vfs.load_module(id, can_use_olean && !m_never_use_olean);
}

template <class Msg>
void server::send_msg(Msg const & m) {
    if (m_quiet) return;
    json j = m.to_json_response();
    unique_lock<mutex> _(m_out_mutex);
    std::cout << j << std::endl;
}

region_of_interest server::get_roi() {
    unique_lock<mutex> _(m_roi_mutex);
    return m_roi;
}

static region_of_interest::checking_mode parse_checking_mode(std::string const & j) {
    if (j == "nothing") return region_of_interest::Nothing;
    if (j == "visible-lines") return region_of_interest::VisibleLines;
    if (j == "visible-lines-and-above") return region_of_interest::VisibleLinesAndAbove;
    if (j == "visible-files") return region_of_interest::VisibleFiles;
    if (j == "open-files") return region_of_interest::OpenFiles;
    throw exception(sstream() << "unknown checking mode: " << j);
}

server::cmd_res server::handle_roi(server::cmd_req const & req) {
    region_of_interest new_roi;
    new_roi.m_check_mode = parse_checking_mode(req.m_payload.at("mode"));
    auto open_files = std::make_shared<std::unordered_map<std::string, std::vector<line_range>>>();
    new_roi.m_open_files = open_files;

    for (auto & f : req.m_payload.at("files")) {
        std::string fn = f.at("file_name");
        std::vector<line_range> ranges;
        for (auto & r : f.at("ranges")) {
            unsigned begin_line = r.at("begin_line");
            unsigned end_line = r.at("end_line");
            ranges.push_back({begin_line, end_line});
        }
        (*open_files)[fn] = ranges;
    }

    for (auto & f : *new_roi.m_open_files) {
        try { m_mod_mgr->get_module(f.first); } catch (...) {}
    }

    {
        unique_lock<mutex> _(m_roi_mutex);
        m_roi = new_roi;
    }
    m_tasks_handler->on_new_roi();
    m_msg_handler->on_new_roi();

    return cmd_res(req.m_seq_num, json());
}

void initialize_server() {
}

void finalize_server() {
}

}
#endif
