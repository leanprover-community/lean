/*
Copyright (c) 2014-2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <string>
#include "library/eval_helper.h"
#include "util/timeit.h"
#include "util/sstream.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/type_checker.h"
#include "kernel/replace_fn.h"
#include "kernel/find_fn.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/scoped_ext.h"
#include "library/trace.h"
#include "library/aliases.h"
#include "library/export_decl.h"
#include "library/protected.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "library/app_builder.h"
#include "library/class.h"
#include "library/user_recursors.h"
#include "library/pp_options.h"
#include "library/attribute_manager.h"
#include "library/aux_recursors.h"
#include "library/private.h"
#include "library/type_context.h"
#include "library/reducible.h"
#include "library/typed_expr.h"
#include "library/documentation.h"
#include "library/placeholder.h"
#include "library/vm/vm.h"
#include "library/vm/vm_io.h"
#include "library/vm/vm_string.h"
#include "library/compiler/vm_compiler.h"
#include "library/tactic/kabstract.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/notation_cmd.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/inductive_cmds.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/print_cmd.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/parse_table.h"
#include "frontends/lean/decl_attributes.h"

namespace lean {
environment section_cmd(parser & p, ast_id & cmd_id) {
    ast_id id = 0; name n;
    if (p.curr_is_identifier())
        std::tie(id, n) = p.check_atomic_id_next("invalid section, atomic identifier expected");
    p.get_ast(cmd_id).push(id);
    p.push_local_scope();
    return push_scope(p.env(), p.ios(), scope_kind::Section, n);
}

// Execute open command
environment execute_open(environment env, io_state const & ios, export_decl const & edecl);

environment replay_export_decls_core(environment env, io_state const & ios, unsigned old_sz) {
    list<export_decl> new_export_decls = get_active_export_decls(env);
    unsigned new_sz = length(new_export_decls);
    lean_assert(new_sz >= old_sz);
    unsigned i = 0;
    for (export_decl const & d : new_export_decls) {
        if (i >= new_sz - old_sz)
            break;
        env = execute_open(env, ios, d);
        i++;
    }
    return env;
}

environment replay_export_decls_core(environment env, io_state const & ios) {
    return replay_export_decls_core(env, ios, 0);
}

environment execute_open(environment env, io_state const & ios, export_decl const & edecl) {
    unsigned fingerprint = 0;
    name const & ns = edecl.m_ns;
    fingerprint = hash(fingerprint, ns.hash());
    unsigned old_export_decls_sz = length(get_active_export_decls(env));
    env = activate_export_decls(env, ns);
    for (auto const & p : edecl.m_renames) {
        fingerprint = hash(hash(fingerprint, p.first.hash()), p.second.hash());
        env = add_expr_alias(env, p.first, p.second);
    }
    for (auto const & n : edecl.m_except_names) {
        fingerprint = hash(fingerprint, n.hash());
    }
    if (!edecl.m_had_explicit) {
        buffer<name> except_names;
        to_buffer(edecl.m_except_names, except_names);
        env = add_aliases(env, ns, edecl.m_as, except_names.size(), except_names.data());
    }
    env = update_fingerprint(env, fingerprint);
    return replay_export_decls_core(env, ios, old_export_decls_sz);
}

environment namespace_cmd(parser & p, ast_id & cmd_id) {
    ast_id id = 0; name n;
    std::tie(id, n) = p.check_decl_id_next("invalid namespace declaration, identifier expected");
    p.get_ast(cmd_id).push(id);
    p.push_local_scope();
    unsigned old_export_decls_sz = length(get_active_export_decls(p.env()));
    environment env = push_scope(p.env(), p.ios(), scope_kind::Namespace, n);
    env = activate_export_decls(env, get_namespace(env));
    return replay_export_decls_core(env, p.ios(), old_export_decls_sz);
}

static environment redeclare_aliases(environment env, parser & p,
                                     local_level_decls old_level_decls,
                                     list<pair<name, expr>> old_entries) {
    environment const & old_env = p.env();
    if (!in_section(old_env))
        return env;
    list<pair<name, expr>> new_entries = p.get_local_entries();
    buffer<pair<name, expr>> to_redeclare;
    unsigned new_len = length(new_entries);
    unsigned old_len = length(old_entries);
    lean_assert(old_len >= new_len);
    name_set popped_locals;
    while (old_len > new_len) {
        pair<name, expr> entry = head(old_entries);
        if (is_local_ref(entry.second))
            to_redeclare.push_back(entry);
        else if (is_local(entry.second))
            popped_locals.insert(mlocal_name(entry.second));
        old_entries = tail(old_entries);
        old_len--;
    }
    name_set popped_levels;
    local_level_decls level_decls = p.get_local_level_decls();
    old_level_decls.for_each([&](name const & n, level const & l) {
            if (is_param(l) && !is_placeholder(l) && !level_decls.contains(n))
                popped_levels.insert(param_id(l));
        });
    for (auto const & entry : to_redeclare) {
        expr new_ref = update_local_ref(entry.second, popped_levels, popped_locals);
        if (!is_constant(new_ref))
            env = p.add_local_ref(env, entry.first, new_ref);
    }
    return env;
}

environment end_scoped_cmd(parser & p, ast_id & cmd_id) {
    local_level_decls level_decls  = p.get_local_level_decls();
    list<pair<name, expr>> entries = p.get_local_entries();
    if (!p.has_local_scopes()) {
        throw exception("invalid 'end', there is no open namespace/section");
    }
    p.pop_local_scope();
    try {
        p.check_break_before();
        if (p.curr_is_identifier()) {
            ast_id id; name n;
            std::tie(id, n) = p.check_id_next("invalid end of scope, identifier expected");
            p.get_ast(cmd_id).push(id);
            environment env = pop_scope(p.env(), p.ios(), n);
            return redeclare_aliases(env, p, level_decls, entries);
        } else {
            p.get_ast(cmd_id).push(0);
            environment env = pop_scope(p.env(), p.ios());
            return redeclare_aliases(env, p, level_decls, entries);
        }
    } catch (break_at_pos_exception & ex) {
        if (p.get_complete()) {
            if (auto n = get_scope_header(p.env())) {
                ex.m_token_info.m_context = break_at_pos_exception::token_context::single_completion;
                ex.m_token_info.m_param = n;
            }
        }
        throw;
    }
}

/* Auxiliary class to setup private naming scope for transient commands such as #check/#reduce/#eval and run_cmd */
class transient_cmd_scope {
    environment            m_env;
    private_name_scope     m_prv_scope;
public:
    transient_cmd_scope(parser & p):
        m_env(p.env()),
        m_prv_scope(true, m_env) {
        p.set_env(m_env);
    }
};

environment check_cmd(parser & p, ast_id & cmd_id) {
    expr e; level_param_names ls;
    transient_cmd_scope cmd_scope(p);
    auto& data = p.get_ast(cmd_id);
    std::tie(e, ls) = parse_local_expr(p, data, "_check");
    type_checker tc(p.env(), true, false);
    expr type = tc.check(e, ls);
    if (is_synthetic_sorry(e) && (is_synthetic_sorry(type) || is_metavar(type))) {
        // do not show useless type-checking results such as ?? : ?M_1
        return p.env();
    }
    auto out              = p.mk_message(data.m_start, p.pos(), INFORMATION);
    formatter fmt         = out.get_formatter();
    unsigned indent       = get_pp_indent(p.get_options());
    format e_fmt    = fmt(e);
    format type_fmt = fmt(type);
    format r = group(e_fmt + space() + colon() + nest(indent, line() + type_fmt));
    out.set_caption("check result") << r;
    out.report();
    return p.env();
}

environment reduce_cmd(parser & p, ast_id & cmd_id) {
    transient_cmd_scope cmd_scope(p);
    bool whnf   = false;
    ast_id id = 0;
    if (p.curr_is_token(get_whnf_tk())) {
        id = p.new_ast("whnf", p.pos()).m_id;
        p.next();
        whnf = true;
    }
    auto& data = p.get_ast(cmd_id).push(id);
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p, data, "_reduce");
    expr r;
    type_context_old ctx(p.env(), p.get_options(), metavar_context(), local_context(), transparency_mode::All);
    if (whnf) {
        r = ctx.whnf(e);
    } else {
        bool eta = false;
        r = normalize(ctx, e, eta);
    }
    auto out = p.mk_message(data.m_start, p.pos(), INFORMATION);
    out.set_caption("reduce result") << r;
    out.report();
    return p.env();
}

environment exit_cmd(parser & p, ast_id & cmd_id) {
    (p.mk_message(p.get_ast(cmd_id).m_start, WARNING) << "using 'exit' to interrupt Lean").report();
    throw interrupt_parser();
}

environment set_option_cmd(parser & p, ast_id & cmd_id) {
    auto& data = p.get_ast(cmd_id);
    auto id_kind = parse_option_name(p, data, "invalid set option, identifier (i.e., option name) expected");
    name id       = id_kind.first;
    option_kind k = id_kind.second;
    if (k == BoolOption) {
        if (p.curr_is_token_or_id(get_true_tk())) {
            data.push(p.new_ast("bool", p.pos(), get_true_tk()).m_id);
            p.set_option(id, true);
        } else if (p.curr_is_token_or_id(get_false_tk())) {
            data.push(p.new_ast("bool", p.pos(), get_false_tk()).m_id);
            p.set_option(id, false);
        } else {
            throw parser_error("invalid Boolean option value, 'true' or 'false' expected", p.pos());
        }
        p.next();
    } else if (k == StringOption) {
        if (!p.curr_is_string())
            throw parser_error("invalid option value, given option is not a string", p.pos());
        auto s = p.get_str_val();
        data.push(p.new_ast("string", p.pos(), s).m_id);
        p.set_option(id, s);
        p.next();
    } else if (k == DoubleOption) {
        ast_id d_id; double d;
        std::tie(d_id, d) = p.parse_double();
        data.push(d_id);
        p.set_option(id, d);
    } else if (k == UnsignedOption || k == IntOption) {
        auto n = p.parse_small_nat();
        data.push(n.first);
        p.set_option(id, n.second);
    } else {
        throw parser_error("invalid option value, 'true', 'false', string, integer or decimal value expected", p.pos());
    }
    environment env = p.env();
    return update_fingerprint(env, p.get_options().hash());
}

static void check_identifier(parser & p, environment const & env, name const & ns, name const & id) {
    name full_id = ns + id;
    if (!env.find(full_id))
        throw parser_error(sstream() << "invalid 'open' command, unknown declaration '" << full_id << "'", p.pos());
}

/** \brief Resolves a reference to a namespace \c n .
    It prefixes \c n with the current scope, and works its way up the stack of namespaces,
    finally trying the root name. If the name is prefixed with \c _root_ then it will always
    resolve to the root name if available.
    Example: suppose the scope is:
       namespace foo
         namespace bla
           namespace boo
              ...
    Then, the procedure tries 'foo.bla.boo'+n, 'foo.bla'+n, 'foo'+n, n.
    If n is of the form '_root_'+m it tries only m. */
optional<name> resolve_namespace_name(environment const & env, name const & n) {
    for (auto const & ns : get_namespaces(env)) {
        name r = ns + n;
        if (is_namespace(env, r))
            return optional<name>(r);
    }
    name new_n = remove_root_prefix(n);
    if (is_namespace(env, new_n))
        return optional<name>(new_n);
    return optional<name>();
}

// open/export id (as id)? (id ...) (renaming id->id id->id) (hiding id ... id)
environment open_export_cmd(parser & p, ast_id cmd_id, bool open) {
    environment env = p.env();
    auto& data = p.get_ast(cmd_id);
    while (true) {
        auto& group = p.new_ast("group", p.pos());
        data.push(group.m_id);
        auto pos   = p.pos();
        ast_id ns_id; name ns;
        std::tie(ns_id, ns) = p.check_id_next("invalid 'open/export' command, identifier expected",
            break_at_pos_exception::token_context::namespc);
        group.push(ns_id);
        optional<name> real_ns = resolve_namespace_name(env, ns);
        if (!real_ns)
            throw parser_error(sstream() << "invalid namespace name '" << ns << "'", pos);
        ns = *real_ns;
        ast_id as_id = 0; name as;
        if (p.curr_is_token_or_id(get_as_tk())) {
            p.next();
            std::tie(as_id, as) = p.check_id_next("invalid 'open/export' command, identifier expected");
        }
        group.push(as_id);
        buffer<name> exception_names;
        buffer<pair<name, name>> renames;
        bool found_explicit = false;
        // Remark: we currently to not allow renaming and hiding of universe levels
        env = mark_namespace_as_open(env, ns);
        while (p.curr_is_token(get_lparen_tk())) {
            auto pos = p.pos();
            p.next();
            if (p.curr_is_token_or_id(get_renaming_tk())) {
                auto& renames_ast = p.new_ast(get_renaming_tk(), pos);
                group.push(renames_ast.m_id);
                p.next();
                while (p.curr_is_identifier()) {
                    name from_id = p.get_name_val();
                    auto& rename = p.new_ast(get_arrow_tk(), p.pos());
                    renames_ast.push(rename.m_id);
                    rename.push(p.new_ast("ident", p.pos(), from_id).m_id);
                    p.next();
                    p.check_token_next(get_arrow_tk(), "invalid 'open/export' command renaming, '->' expected");
                    ast_id to_ast; name to_id;
                    std::tie(to_ast, to_id) = p.check_id_next("invalid 'open/export' command renaming, identifier expected");
                    rename.push(to_ast);
                    check_identifier(p, env, ns, from_id);
                    exception_names.push_back(from_id);
                    renames.emplace_back(as+to_id, ns+from_id);
                }
            } else if (p.curr_is_token_or_id(get_hiding_tk())) {
                auto& hides = p.new_ast(get_hiding_tk(), pos);
                group.push(hides.m_id);
                p.next();
                while (p.curr_is_identifier()) {
                    name id = p.get_name_val();
                    hides.push(p.new_ast("ident", p.pos(), id).m_id);
                    p.next();
                    check_identifier(p, env, ns, id);
                    exception_names.push_back(id);
                }
            } else if (p.curr_is_identifier()) {
                auto& explicit_ast = p.new_ast("explicit", pos);
                group.push(explicit_ast.m_id);
                found_explicit = true;
                while (p.curr_is_identifier()) {
                    name id = p.get_name_val();
                    explicit_ast.push(p.new_ast("ident", p.pos(), id).m_id);
                    p.next();
                    check_identifier(p, env, ns, id);
                    renames.emplace_back(as+id, ns+id);
                }
            } else {
                throw parser_error("invalid 'open/export' command option, "
                                   "identifier, 'hiding' or 'renaming' expected", p.pos());
            }
            if (found_explicit && !exception_names.empty())
                throw parser_error("invalid 'open/export' command option, "
                                   "mixing explicit and implicit 'open/export' options", p.pos());
            p.check_token_next(get_rparen_tk(), "invalid 'open/export' command option, ')' expected");
        }
        export_decl edecl(ns, as, found_explicit, renames, exception_names);
        env = execute_open(env, p.ios(), edecl);
        if (!open) {
            env = add_export_decl(env, edecl);
        }
        if (!p.curr_is_identifier())
            break;
    }
    return env;
}
environment open_cmd(parser & p, ast_id & cmd_id) { return open_export_cmd(p, cmd_id, true); }
static environment export_cmd(parser & p, ast_id & cmd_id) { return open_export_cmd(p, cmd_id, false); }

static environment local_cmd(parser & p, ast_id & cmd_id, cmd_meta const & meta) {
    if (p.curr_is_token_or_id(get_attribute_tk())) {
        p.next();
        return local_attribute_cmd(p, cmd_id, meta);
    } else {
        return local_notation_cmd(p, cmd_id);
    }
}

static environment help_cmd(parser & p, ast_id & cmd_id) {
    auto& data = p.get_ast(cmd_id);
    auto rep = p.mk_message(data.m_start, INFORMATION);
    if (p.curr_is_token_or_id(get_options_tk())) {
        data.push(p.new_ast(get_options_tk(), p.pos()).m_id);
        p.next();
        rep.set_end_pos(p.pos());
        auto decls = get_option_declarations();
        decls.for_each([&](name const &, option_declaration const & opt) {
                rep << "  " << opt.get_name() << " (" << opt.kind() << ") "
                    << opt.get_description() << " (default: " << opt.get_default_value() << ")\n";
            });
    } else if (p.curr_is_token_or_id(get_commands_tk())) {
        data.push(p.new_ast(get_commands_tk(), p.pos()).m_id);
        p.next();
        buffer<name> ns;
        cmd_table const & cmds = p.cmds();
        cmds.for_each([&](name const & n, cmd_info const &) {
                ns.push_back(n);
            });
        std::sort(ns.begin(), ns.end());
        rep.set_end_pos(p.pos());
        for (name const & n : ns) {
            rep << "  " << n << ": " << cmds.find(n)->get_descr() << "\n";
        };
    } else {
        rep << "help options  : describe available options\n"
            << "help commands : describe available commands\n";
    }
    rep.report();
    return p.env();
}

static environment init_quotient_cmd(parser & p, ast_id &) {
    return module::declare_quotient(p.env());
}

/*
   Temporary procedure that converts metavariables in \c e to metavar_context metavariables.
   After we convert the frontend to type_context_old, we will not need to use this procedure.
*/
static expr convert_metavars(metavar_context & mctx, expr const & e) {
    expr_map<expr> cache;

    std::function<expr(expr const & e)> convert = [&](expr const & e) {
        return replace(e, [&](expr const e, unsigned) {
                if (is_metavar(e)) {
                    auto it = cache.find(e);
                    if (it != cache.end())
                        return some_expr(it->second);
                    expr m = mctx.mk_metavar_decl(local_context(), convert(mlocal_type(e)));
                    cache.insert(mk_pair(e, m));
                    return some_expr(m);
                } else {
                    return none_expr();
                }
            });
    };
    return convert(e);
}

static environment unify_cmd(parser & p, ast_id & cmd_id) {
    transient_cmd_scope cmd_scope(p);
    environment const & env = p.env();
    auto& data = p.get_ast(cmd_id);
    expr e1; level_param_names ls1;
    std::tie(e1, ls1) = parse_local_expr(p, data, "_unify");
    p.check_token_next(get_comma_tk(), "invalid #unify command, proper usage \"#unify e1, e2\"");
    expr e2; level_param_names ls2;
    std::tie(e2, ls2) = parse_local_expr(p, data, "_unify");
    metavar_context mctx;
    local_context   lctx;
    e1 = convert_metavars(mctx, e1);
    e2 = convert_metavars(mctx, e2);
    auto rep = p.mk_message(data.m_start, p.pos(), INFORMATION);
    rep << e1 << " =?= " << e2 << "\n";
    type_context_old ctx(env, p.get_options(), mctx, lctx, transparency_mode::Semireducible);
    bool success = ctx.is_def_eq(e1, e2);
    if (success)
        rep << ctx.instantiate_mvars(e1) << " =?= " << ctx.instantiate_mvars(e2) << "\n";
    rep << (success ? "unification successful" : "unification failed");
    rep.report();
    return env;
}

static environment compile_cmd(parser & p, ast_id & cmd_id) {
    auto pos = p.pos();
    ast_id id = 0; name n;
    std::tie(id, n) = p.check_constant_next("invalid #compile command, constant expected");
    p.get_ast(cmd_id).push(id);
    declaration d = p.env().get(n);
    if (!d.is_definition())
        throw parser_error("invalid #compile command, declaration is not a definition", pos);
    return vm_compile(p.env(), p.get_options(), d);
}

static environment eval_cmd(parser & p, ast_id & cmd_id) {
    transient_cmd_scope cmd_scope(p);
    auto pos = p.pos();
    auto& data = p.get_ast(cmd_id);
    expr e; level_param_names ls;
    std::tie(e, ls) = parse_local_expr(p, data, "_eval", /* relaxed */ false);
    if (has_synthetic_sorry(e))
        return p.env();

    type_context_old tc(p.env(), transparency_mode::All);
    auto type = tc.infer(e);
    bool has_repr_inst = false;

    /* Check if resultant type has an instance of has_repr */
    try {
        expr has_repr_type = mk_app(tc, get_has_repr_name(), type);
        optional<expr> repr_instance = tc.mk_class_instance(has_repr_type);
        if (repr_instance) {
            /* Modify the 'program' to (repr e) */
            e             = mk_app(tc, get_repr_name(), type, *repr_instance, e);
            type          = tc.infer(e);
            has_repr_inst = true;
        }
    } catch (exception &) {}

    // Close under locals
    collected_locals locals;
    collect_locals(e, locals);
    for (auto & l : locals.get_collected()) {
        e    = Fun(l, e);
        type = Pi(l, type);
    }

    name fn_name = "_main";
    auto new_env = compile_expr(p.env(), p.get_options(), fn_name, ls, type, e, pos);

    auto out = p.mk_message(data.m_start, p.pos(), INFORMATION);
    out.set_caption("eval result");
    scope_traces_as_messages scope_traces(p.get_stream_name(), data.m_start);
    bool should_report = false;

    auto run = [&] {
        eval_helper fn(new_env, p.get_options(), fn_name);
        try {
            if (!fn.try_exec()) {
                auto r = fn.invoke_fn();
                should_report = true;
                if (!has_repr_inst) {
                    (p.mk_message(data.m_start, WARNING) << "result type does not have an instance of type class 'has_repr', dumping internal representation").report();
                }
                if (is_constant(fn.get_type(), get_string_name())) {
                    out << to_string(r);
                } else {
                    display(out.get_text_stream().get_stream(), r);
                }
            }
        } catch (throwable & t) {
            p.mk_message(data.m_start, ERROR).set_exception(t).report();
        }
        if (fn.get_profiler().enabled()) {
            if (fn.get_profiler().get_snapshots().display("#eval", p.get_options(), out.get_text_stream().get_stream()))
                should_report = true;
        }
    };

    if (p.profiling()) {
        timeit timer(out.get_text_stream().get_stream(), "eval time");
        run();
        should_report = true;
    } else {
        run();
    }

    if (should_report) out.report();

    return p.env();
}

struct declare_trace_modification : public modification {
    LEAN_MODIFICATION("decl_trace")

    name m_cls;

    declare_trace_modification(name const & cls) : m_cls(cls) {}
    declare_trace_modification() {}

    void perform(environment &) const override {
        // TODO(gabriel): this is just fundamentally wrong
        register_trace_class(m_cls);
    }

    void serialize(serializer & s) const override {
        s << m_cls;
    }

    static std::shared_ptr<modification const> deserialize(deserializer & d) {
        return std::make_shared<declare_trace_modification>(read_name(d));
    }
};

environment declare_trace_cmd(parser & p, ast_id & cmd_id) {
    auto cls = p.check_id_next("invalid declare_trace command, identifier expected");
    p.get_ast(cmd_id).push(cls.first);
    return module::add_and_perform(p.env(), std::make_shared<declare_trace_modification>(cls.second));
}

environment add_key_equivalence_cmd(parser & p, ast_id & cmd_id) {
    ast_id id1, id2; name h1, h2;
    std::tie(id1, h1) = p.check_constant_next("invalid add_key_equivalence command, constant expected");
    std::tie(id2, h2) = p.check_constant_next("invalid add_key_equivalence command, constant expected");
    p.get_ast(cmd_id).push(id1).push(id2);
    return add_key_equivalence(p.env(), h1, h2);
}

static environment run_command_cmd(parser & p, ast_id & cmd_id) {
    transient_cmd_scope cmd_scope(p);
    module::scope_pos_info scope_pos(p.pos());
    environment env      = p.env();
    options opts         = p.get_options();
    metavar_context mctx;
    expr tactic          = p.parse_expr();
    p.get_ast(cmd_id).push(p.get_id(tactic));
    expr try_triv        = mk_app(mk_constant(get_tactic_try_name()), mk_constant(get_tactic_triv_name()));
    tactic               = mk_app(mk_constant(get_has_bind_and_then_name()), tactic, try_triv);
    tactic               = mk_typed_expr(mk_tactic_unit(), tactic);
    expr val             = mk_typed_expr(mk_true(), mk_by(tactic));
    bool check_unassigned = false;
    bool recover_from_errors = true;
    local_context lctx;
    lctx.freeze_local_instances(local_instances());
    elaborate(env, opts, "_run_command", mctx, lctx, val, check_unassigned, recover_from_errors);
    return env;
}

environment import_cmd(parser & p, ast_id & cmd_id) {
    throw parser_error("invalid 'import' command, it must be used in the beginning of the file", p.get_ast(cmd_id).m_start);
}

environment hide_cmd(parser & p, ast_id & cmd_id) {
    buffer<name> ids;
    auto& data = p.get_ast(cmd_id);
    while (p.curr_is_identifier()) {
        name id = p.get_name_val();
        data.push(p.new_ast("ident", p.pos(), id).m_id);
        p.next();
        ids.push_back(id);
    }
    if (ids.empty())
        throw parser_error("invalid 'hide' command, identifier expected", data.m_start);
    environment new_env = p.env();
    for (name id : ids) {
        if (get_expr_aliases(new_env, id)) {
            new_env = erase_expr_aliases(new_env, id);
        } else {
            /* TODO(Leo): check if `id` is a declaration and hide it too. */
            throw parser_error(sstream() << "invalid 'hide' command, '" << id << "' is not an alias",
                               data.m_start);
        }
    }
    return new_env;
}

void init_cmd_table(cmd_table & r) {
    add_cmd(r, cmd_info("open",              "create aliases for declarations, and use objects defined in other namespaces",
                        open_cmd));
    add_cmd(r, cmd_info("export",            "create aliases for declarations", export_cmd));
    add_cmd(r, cmd_info("set_option",        "set configuration option", set_option_cmd));
    add_cmd(r, cmd_info("#exit",             "exit", exit_cmd, false));
    add_cmd(r, cmd_info("#print",            "print a string or information about an indentifier", print_cmd));
    add_cmd(r, cmd_info("section",           "open a new section", section_cmd));
    add_cmd(r, cmd_info("namespace",         "open a new namespace", namespace_cmd));
    add_cmd(r, cmd_info("end",               "close the current namespace/section", end_scoped_cmd));
    add_cmd(r, cmd_info("#check",            "type check given expression, and display its type", check_cmd));
    add_cmd(r, cmd_info("#reduce",           "reduce given expression", reduce_cmd));
    add_cmd(r, cmd_info("#eval",             "evaluate given expression using VM", eval_cmd));
    add_cmd(r, cmd_info("local",             "define local attributes or notation", local_cmd));
    add_cmd(r, cmd_info("#help",             "brief description of available commands and options", help_cmd));
    add_cmd(r, cmd_info("init_quotient",     "initialize quotient type computational rules", init_quotient_cmd));
    add_cmd(r, cmd_info("declare_trace",     "declare a new trace class (for debugging Lean tactics)", declare_trace_cmd));
    add_cmd(r, cmd_info("add_key_equivalence", "register that to symbols are equivalence for key-matching", add_key_equivalence_cmd));
    add_cmd(r, cmd_info("run_cmd",           "execute an user defined command at top-level", run_command_cmd));
    add_cmd(r, cmd_info("import",            "import module(s)", import_cmd));
    add_cmd(r, cmd_info("hide",              "hide aliases in the current scope", hide_cmd));
    add_cmd(r, cmd_info("#unify",            "(for debugging purposes)", unify_cmd));
    add_cmd(r, cmd_info("#compile",          "(for debugging purposes)", compile_cmd));

    register_decl_cmds(r);
    register_inductive_cmds(r);
    register_structure_cmd(r);
    register_notation_cmds(r);
    // register_tactic_hint_cmd(r);
}

static cmd_table * g_cmds = nullptr;

cmd_table get_builtin_cmds() {
    return *g_cmds;
}

void initialize_builtin_cmds() {
    g_cmds = new cmd_table();
    init_cmd_table(*g_cmds);
    declare_trace_modification::init();
}

void finalize_builtin_cmds() {
    declare_trace_modification::finalize();
    delete g_cmds;
}
}
