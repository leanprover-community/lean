/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#include "library/vm/vm_parser.h"
#include <string>
#include <iostream>
#include <vector>
#include "library/constants.h"
#include "library/explicit.h"
#include "library/num.h"
#include "library/quote.h"
#include "library/trace.h"
#include "library/placeholder.h"
#include "library/vm/interaction_state_imp.h"
#include "library/tactic/elaborate.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_pos_info.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/inductive_cmds.h"
#include "frontends/lean/tactic_notation.h"
#include "util/utf8.h"

namespace lean {

struct lean_parser_state {
    parser * m_p;
};

bool is_ts_safe(lean_parser_state const &) { return false; }
template struct interaction_monad<lean_parser_state>;
typedef interaction_monad<lean_parser_state> lean_parser;

#define TRY try {
#define CATCH } catch (break_at_pos_exception const & ex) { throw; }\
                catch (exception const & ex) { return lean_parser::mk_exception(ex, s); }

pair<ast_id, vm_obj> run_parser(parser & p, expr const & spec, buffer<vm_obj> const & args, bool allow_profiler) {
    type_context_old ctx(p.env(), p.get_options());
    auto& data = p.new_ast("parse", p.pos());
    auto old = p.set_vm_parse_parent(data.m_id);
    auto r = lean_parser::evaluator(ctx, p.get_options(), allow_profiler)(spec, args, {&p});
    p.set_vm_parse_parent(old);
    return {data.m_id, lean_parser::get_success_value(r)};
}

expr parse_interactive_param(parser & p, ast_data & parent, expr const & param_ty) {
    lean_assert(is_app_of(param_ty, get_interactive_parse_name()));
    buffer<expr> param_args;
    get_app_args(param_ty, param_args);
    // alpha, parser alpha, lean.parser.reflectable alpha
    lean_assert(param_args.size() == 3);
    if (!closed(param_args[1])) {
        throw elaborator_exception(param_args[1], "error running user-defined parser: must be closed expression");
    }
    try {
        expr pr = mk_app({mk_constant(get_lean_parser_reflectable_expr_name()),
            param_args[0], param_args[1], param_args[2]});
        ast_id id; vm_obj obj;
        std::tie(id, obj) = run_parser(p, pr);
        expr r = to_expr(obj);
        if (!is_app_of(r, get_expr_subst_name())) { // HACK
            r = mk_as_is(r);
        }
        r.set_tag(nulltag);
        p.finalize_ast(id, r);
        parent.push(id);
        return r;
    } catch (exception & ex) {
        if (!p.has_error_recovery()) throw;
        p.mk_message(ERROR).set_exception(ex).report();
        return p.mk_sorry(p.pos(), true);
    }
}

struct vm_decl_attributes : public vm_external {
    decl_attributes m_val;
    vm_decl_attributes(decl_attributes const & v):m_val(v) {}
    virtual ~vm_decl_attributes() {}
    virtual void dealloc() override { this->~vm_decl_attributes(); get_vm_allocator().deallocate(sizeof(vm_decl_attributes), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_decl_attributes(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_decl_attributes))) vm_decl_attributes(m_val); }
    virtual unsigned int hash() { return 0; }
};

static decl_attributes const & to_decl_attributes(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_decl_attributes*>(to_external(o)));
    return static_cast<vm_decl_attributes*>(to_external(o))->m_val;
}

static vm_obj to_obj(decl_attributes const & n) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_decl_attributes))) vm_decl_attributes(n));
}

static vm_obj to_obj(decl_modifiers const & mods) {
    return mk_vm_constructor(0, {
            mk_vm_bool(mods.m_is_private),
            mk_vm_bool(mods.m_is_protected),
            mk_vm_bool(mods.m_is_meta),
            mk_vm_bool(mods.m_is_mutual),
            mk_vm_bool(mods.m_is_noncomputable),
    });
}

vm_obj to_obj(cmd_meta const & meta) {
    return mk_vm_constructor(0, {
            to_obj(meta.m_attrs),
            to_obj(meta.m_modifiers),
            to_obj(meta.m_doc_string)
    });
}

decl_modifiers to_decl_modifiers(vm_obj const & o) {
    lean_always_assert(cidx(o) == 0);
    decl_modifiers mods;
    if (to_bool(cfield(o, 0))) {
        mods.m_is_private = true;
    }
    if (to_bool(cfield(o, 1))) {
        mods.m_is_protected = true;
    }
    if (to_bool(cfield(o, 2))) {
        mods.m_is_meta = true;
    }
    if (to_bool(cfield(o, 3))) {
        mods.m_is_mutual = true;
    }
    if (to_bool(cfield(o, 4))) {
        mods.m_is_noncomputable = true;
    }
    return mods;
}

cmd_meta to_cmd_meta(vm_obj const & o) {
    lean_always_assert(cidx(o) == 0);
    optional<std::string> doc_string;
    if (!is_none(cfield(o, 2))) {
        doc_string = some(to_string(get_some_value(cfield(o, 2))));
    }
    return {to_decl_attributes(cfield(o, 0)), to_decl_modifiers(cfield(o, 1)), doc_string};
}

vm_obj to_obj(lean_parser_state const & s) {
    return lean_parser::to_obj(s);
}

vm_obj vm_parser_state_env(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    return to_obj(s.m_p->env());
}

vm_obj vm_parser_state_options(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    return to_obj(s.m_p->get_options());
}

vm_obj vm_parser_state_cur_pos(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    return to_obj(s.m_p->pos());
}

vm_obj vm_parser_set_env(vm_obj const & vm_env, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    s.m_p->set_env(to_env(vm_env));
    return lean_parser::mk_success(s);
}

vm_obj vm_parser_ident(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    TRY;
        auto _ = s.m_p->no_error_recovery_scope();
        ast_id id; name ident;
        std::tie(id, ident) = s.m_p->check_id_next("identifier expected");
        s.m_p->push_from_vm_parse(id);
        return lean_parser::mk_success(to_obj(ident), s);
    CATCH;
}

vm_obj vm_parser_small_nat(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    TRY;
        auto _ = s.m_p->no_error_recovery_scope();
        ast_id id; unsigned n;
        std::tie(id, n) = s.m_p->parse_small_nat();
        s.m_p->push_from_vm_parse(id);
        return lean_parser::mk_success(mk_vm_nat(n), s);
    CATCH;
}

vm_obj vm_parser_tk(vm_obj const & vm_tk, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    TRY;
        name tk = to_string(vm_tk);
        if (!s.m_p->curr_is_token(tk))
            throw parser_error(sstream() << "'" << tk << "' expected", s.m_p->pos());
        s.m_p->push_from_vm_parse(s.m_p->new_ast("token", s.m_p->pos(), tk).m_id);
        s.m_p->next();
        return lean_parser::mk_success(s);
    CATCH;
}

vm_obj vm_parser_list_include_var_names(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    buffer<name> r;
    s.m_p->get_include_var_names(r);
    return lean_parser::mk_success(to_obj(r), s);
}

vm_obj vm_parser_list_available_include_vars(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    buffer<expr> r;
    s.m_p->get_available_include_var_names(r);
    return lean_parser::mk_success(to_obj(r), s);
}

vm_obj vm_parser_include_var(vm_obj const & v, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    auto n = to_name(v);
    if (s.m_p->get_local(n)) {
        if (!s.m_p->is_include_variable(n)) {
            s.m_p->include_variable(to_name(v));
            return lean_parser::mk_success(s);
        } else {
            return lean_parser::mk_exception(sstream() << "invalid include command, '" << n << "' has already been included", s);
        }
    }  else {
        return lean_parser::mk_exception(sstream() << "invalid include/omit command, '" << n << "' is not a parameter/variable", s);
    }
}

vm_obj vm_parser_omit_var(vm_obj const & v, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    auto n = to_name(v);
    if (s.m_p->get_local(n)) {
        if (s.m_p->is_include_variable(n)) {
            s.m_p->omit_variable(n);
            return lean_parser::mk_success(s);
        } else {
            return lean_parser::mk_exception(sstream() << "invalid omit command, '" << n << "' has not been included", s);
        }
    }  else {
        return lean_parser::mk_exception(sstream() << "invalid include/omit command, '" << n << "' is not a parameter/variable", s);
    }
}

vm_obj vm_parser_add_local(vm_obj const & e, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    s.m_p->add_local(to_expr(e), true);
    return lean_parser::mk_success(s);
}

vm_obj vm_parser_add_local_level(vm_obj const & e, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    auto n = to_name(e);
    s.m_p->add_local_level(n, mk_param_univ(n), true);
    return lean_parser::mk_success(s);
}

vm_obj vm_parser_push_local_scope(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    s.m_p->push_local_scope();
    return lean_parser::mk_success(s);
}

vm_obj vm_parser_pop_local_scope(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    if (s.m_p->has_local_scopes()) {
        s.m_p->pop_local_scope();
        return lean_parser::mk_success(s);
    } else {
        return lean_parser::mk_exception("no pushed local scopes", s);
    }
}

vm_obj vm_parser_pexpr(vm_obj const & vm_rbp, vm_obj const & vm_pat, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    TRY;
        /* The macro used to encode pattern matching and recursive equations
           currently stores whether it is meta or not.
           This information is retrieved from a thread local object.
           In tactic blocks, we allow untrusted code even if the surrounding declaration is non meta.
           We use the auxiliary class `meta_definition_scope` to temporarily update the thread local object.
           A quoted expression occurring in a tactic should use the original flag.
           The auxiliary class `restore_decl_meta_scope` is used to restore it.

           Remark: I realize this is hackish, but it addresses the issue raised at #1890.
        */
        restore_decl_meta_scope scope;
        auto rbp = to_unsigned(vm_rbp);
        auto pat = to_bool(vm_pat);
        auto pos = s.m_p->pos();
        optional<expr> e;
        if (pat) {
            e = s.m_p->maybe_parse_pattern(rbp);
        } else {
            e = s.m_p->maybe_parse_expr(rbp);
        }
        if (e) {
            auto id = s.m_p->new_ast(pat ? "pat" : "expr", pos).push(s.m_p->get_id(*e)).m_id;
            s.m_p->push_from_vm_parse(id);
            return lean_parser::mk_success(to_obj(*e), s);
        } else {
            throw parser_error(sstream() << "expression expected", s.m_p->pos());
        }
    CATCH;
}

vm_obj vm_parser_itactic_reflected(vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    TRY;
        metavar_context mctx;
        auto _ = s.m_p->no_error_recovery_scope();
        expr e = parse_nested_interactive_tactic(*s.m_p, get_tactic_name(), true);
        s.m_p->push_from_vm_parse(s.m_p->get_id(e));
        vm_obj r = to_obj(s.m_p->elaborate({}, mctx, e, false).first);
        r = mk_vm_constructor(0, r, r);
        return lean_parser::mk_success(r, s);
    CATCH;
}

vm_obj vm_parser_skip_info(vm_obj const &, vm_obj const & vm_p, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    return s.m_p->without_break_at_pos<vm_obj>([&]() {
        return invoke(vm_p, o);
    });
}

vm_obj vm_parser_set_goal_info_pos(vm_obj const &, vm_obj const & vm_p, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    auto pos = s.m_p->pos();
    try {
        return invoke(vm_p, o);
    } catch (break_at_pos_exception & ex) {
        ex.report_goal_pos(pos);
        throw;
    }
}

vm_obj vm_parser_with_input(vm_obj const &, vm_obj const & vm_p, vm_obj const & vm_input, vm_obj const & o) {
    auto const & s = lean_parser::to_state(o);
    std::string input = to_string(vm_input);
    std::istringstream strm(input);
    vm_obj vm_state; pos_info pos;
    auto old_id = s.m_p->get_vm_parse_parent();
    auto& new_data = s.m_p->new_ast("with_input", s.m_p->pos());
    s.m_p->push_from_vm_parse(new_data.m_id);
    s.m_p->set_vm_parse_parent(new_data.m_id);
    auto _ = s.m_p->no_error_recovery_scope();
    TRY;
        std::tie(vm_state, pos) = s.m_p->with_input<vm_obj>(strm, [&]() {
            return invoke(vm_p, o);
        });
    CATCH;
    s.m_p->set_vm_parse_parent(old_id);

    if (lean_parser::is_result_exception(vm_state)) {
        return vm_state;
    }
    auto vm_res = lean_parser::get_success_value(vm_state);

    // figure out remaining string from end position
    pos_info pos2 = {1, 0};
    unsigned spos = 0;
    while (pos2 < pos) {
        lean_assert(spos < input.size());
        if (input[spos] == '\n') {
            pos2.first++;
            pos2.second = 0;
        } else {
            pos2.second++;
        }
        spos += get_utf8_size(input[spos]);
    }
    new_data.m_value = std::to_string(spos);
    vm_res = mk_vm_pair(vm_res, to_obj(input.substr(spos)));
    return lean_parser::mk_success(vm_res, lean_parser::get_success_state(vm_state));
}
static vm_obj vm_parser_command_like(vm_obj const & vm_s) {
    auto s = lean_parser::to_state(vm_s);
    TRY;
        auto& data = s.m_p->new_ast("command", s.m_p->pos());
        s.m_p->push_from_vm_parse(data.m_id);
        s.m_p->parse_command_like(&data);
        return lean_parser::mk_success(s);
    CATCH;
}


static vm_obj interactive_decl_attributes_apply(vm_obj const & vm_attrs, vm_obj const & vm_n, vm_obj const & vm_s) {
    auto s = lean_parser::to_state(vm_s);
    TRY;
        auto env = to_decl_attributes(vm_attrs).apply(s.m_p->env(), get_dummy_ios(), to_name(vm_n));
        s.m_p->set_env(env);
        return lean_parser::mk_success({s.m_p});
    CATCH;
}

static vm_obj to_obj(single_inductive_decl const & d) {
    return mk_vm_constructor(0, {to_obj(d.m_attrs), to_obj(d.m_expr), to_obj(d.m_intros)});
}

static vm_obj to_obj(inductive_decl const & d) {
    return mk_vm_constructor(0, {to_obj(d.m_lp_names), to_obj(d.m_params),
                                 to_vm_list(to_list(d.m_decls), [](single_inductive_decl const & d) { return to_obj(d); })});
}

static vm_obj interactive_inductive_decl_parse(vm_obj const & vm_meta, vm_obj const & vm_s) {
    auto s = lean_parser::to_state(vm_s);
    TRY;
        auto& data = s.m_p->new_ast("inductive", s.m_p->pos());
        s.m_p->push_from_vm_parse(data.m_id);
        auto decl = parse_inductive_decl(*s.m_p, data.m_id, to_cmd_meta(vm_meta));
        return lean_parser::mk_success(to_obj(decl), s);
    CATCH;
}

static vm_obj interactive_parse_binders(vm_obj const & vm_rbp, vm_obj const & vm_s) {
    auto s = lean_parser::to_state(vm_s);
    TRY;
        buffer<expr> binders;
        auto& data = s.m_p->new_ast("binders", s.m_p->pos());
        s.m_p->push_from_vm_parse(data.m_id);
        s.m_p->parse_binders(&data, binders, to_unsigned(vm_rbp));
        return lean_parser::mk_success(to_obj(binders), s);
    CATCH;
}

static vm_obj vm_parser_of_tactic(vm_obj const &, vm_obj const & tac, vm_obj const & vm_s) {
    auto const & s = lean_parser::to_state(vm_s);
    tactic_state ts = mk_tactic_state_for(s.m_p->env(), s.m_p->get_options(), name("_parser_of_tactic"),
                                          metavar_context(), local_context(), mk_true());
    try {
        vm_obj r = invoke(tac, to_obj(ts));
        if (tactic::is_result_success(r)) {
            vm_obj a = tactic::get_success_value(r);
            tactic_state new_ts = tactic::to_state(tactic::get_success_state(r));
            s.m_p->set_env(new_ts.env());
            return lean_parser::mk_success(a, s);
        } else {
            /* Remark: the following command relies on the fact that
               `tactic` and `parser` are both implemented using interaction_monad */
            return lean_parser::update_exception_state(r, s);
        }
    } catch (exception & ex) {
        return lean_parser::mk_exception(ex, s);
    }
}

/** α:Type → parser α → string → tactic_state → result tactic_state α */
static vm_obj vm_parser_run(vm_obj const &/*α*/, vm_obj const & vm_p, vm_obj const & vm_ts) {
    auto s = tactic::to_state(vm_ts);
    io_state const & ios = get_global_ios();
    try {
      std::string input = "";
      std::istringstream input_stream(input, std::ios_base::out);
      parser p(s.env(), ios, mk_dummy_loader(), input_stream, "dummy file");
      lean_parser_state lps = {&p};
      vm_obj result = invoke(vm_p, interaction_monad<lean_parser_state>::to_obj(lps));
      if (lean_parser::is_result_success(result)) {
          return tactic::mk_success(lean_parser::get_success_value(result), s);
      } else {
          return tactic::update_exception_state(result, s);
      }
    } catch (exception & ex) {
      return tactic::mk_exception(ex, s);
    }
}

void initialize_vm_parser() {
    DECLARE_VM_BUILTIN(name({"lean", "parser_state", "env"}),         vm_parser_state_env);
    DECLARE_VM_BUILTIN(name({"lean", "parser_state", "options"}),     vm_parser_state_options);
    DECLARE_VM_BUILTIN(name({"lean", "parser_state", "cur_pos"}),     vm_parser_state_cur_pos);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "run"}),               vm_parser_run);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "ident"}),             vm_parser_ident);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "command_like"}),      vm_parser_command_like);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "push_local_scope"}),  vm_parser_push_local_scope);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "pop_local_scope"}),   vm_parser_pop_local_scope);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "small_nat"}),         vm_parser_small_nat);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "set_env"}),           vm_parser_set_env);
    DECLARE_VM_BUILTIN(get_lean_parser_tk_name(),                     vm_parser_tk);
    DECLARE_VM_BUILTIN(get_lean_parser_pexpr_name(),                  vm_parser_pexpr);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "itactic_reflected"}), vm_parser_itactic_reflected);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "skip_info"}),         vm_parser_skip_info);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "add_local"}),         vm_parser_add_local);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "list_available_include_vars"}), vm_parser_list_available_include_vars);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "add_local_level"}),   vm_parser_add_local_level);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "list_include_var_names"}), vm_parser_list_include_var_names);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "include_var"}),        vm_parser_include_var);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "omit_var"}),           vm_parser_omit_var);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "set_goal_info_pos"}), vm_parser_set_goal_info_pos);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "with_input"}),        vm_parser_with_input);
    DECLARE_VM_BUILTIN(name({"lean", "parser", "of_tactic"}),         vm_parser_of_tactic);
    DECLARE_VM_BUILTIN(name({"interactive", "decl_attributes", "apply"}), interactive_decl_attributes_apply);
    DECLARE_VM_BUILTIN(name({"interactive", "inductive_decl", "parse"}),  interactive_inductive_decl_parse);
    DECLARE_VM_BUILTIN(name({"interactive", "parse_binders"}),            interactive_parse_binders);
}

void finalize_vm_parser() {
}

}
